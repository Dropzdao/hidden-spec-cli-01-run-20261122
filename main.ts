// main.ts is mend, one patch tool for every AI edit format.
// Usage: node main.ts [--format=NAME] [--check] [--strict] [PATCH]
// Reads a patch from a file, from '-' (stdin), or from stdin when no PATCH
// is given, and applies its edits to the files under the current directory.
// Formats: unified (git-style diff), search-replace (<<<<<<< SEARCH blocks),
// v4a (*** Begin Patch ... *** End Patch), json (array or JSON Lines), and
// auto (detect from the patch text). See SPEC.md for the full contract.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}

class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const parts = text.split('\n');
  if (parts[parts.length - 1] === '') parts.pop();
  return parts.map((line) => (line.endsWith('\r') ? line.slice(0, -1) : line));
}

function safe(p: string): boolean {
  if (p === '') return false;
  if (p.startsWith('/')) return false;
  if (p.includes('\\')) return false;
  for (const part of p.split('/')) {
    if (part === '' || part === '.' || part === '..') return false;
  }
  return true;
}

// ---------------------------------------------------------------------------
// File lines (SPEC section 1): a file's line break is CRLF when its first
// line feed follows a carriage return, otherwise LF. `lines` is the text
// split at that break, `final` says whether the text ends with a break.
// An empty file has no lines.
// ---------------------------------------------------------------------------

interface FileState {
  br: '\n' | '\r\n';
  lines: string[];
  final: boolean;
}

function splitFile(text: string): FileState {
  if (text === '') return { br: '\n', lines: [], final: false };
  const nl = text.indexOf('\n');
  const br: '\n' | '\r\n' = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const final = text.endsWith(br);
  if (final) parts.pop();
  return { br, lines: parts, final };
}

function joinFile(st: FileState): string {
  if (st.lines.length === 0) return '';
  return st.lines.join(st.br) + (st.final ? st.br : '');
}

// ---------------------------------------------------------------------------
// Matching (SPEC section 5): an old block O is found at the first of three
// tiers with at least one occurrence. Tier 0 is exact; tier 1 ignores
// trailing spaces/tabs on both sides; tier 2 ignores leading and trailing
// spaces/tabs on both sides. --strict allows tier 0 only.
// ---------------------------------------------------------------------------

const lead = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
};

function lineEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return a.replace(/[ \t]+$/, '') === b.replace(/[ \t]+$/, '');
  return a.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '') === b.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

/** All 0-based positions where O occurs in `lines` at `tier`, from `from`. */
function occurrences(lines: string[], o: string[], tier: number, from = 0): number[] {
  const out: number[] = [];
  if (o.length === 0) return out;
  for (let i = from; i + o.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (!lineEq(lines[i + j]!, o[j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** First tier with an occurrence at/after `from`, or null. */
function firstTier(
  lines: string[],
  o: string[],
  strict: boolean,
  from = 0,
): { tier: number; occ: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const occ = occurrences(lines, o, t, from);
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}

interface OItem {
  text: string;
  ctx: boolean;
}

/**
 * Replace the matched lines at `pos` with N. A context line of N is written
 * as the file's own matched line, never the patch's. At tier 2 every other
 * (non-context) line of N is re-indented: P is the leading whitespace of
 * O's first line, F that of the file's first matched line; a non-empty,
 * non-whitespace-only N line starting with P has P replaced by F.
 */
function applyO(lines: string[], o: OItem[], n: OItem[], pos: number, tier: number): string[] {
  const ctxFile: string[] = [];
  o.forEach((it, k) => {
    if (it.ctx) ctxFile.push(lines[pos + k]!);
  });
  const P = o.length > 0 ? lead(o[0]!.text) : '';
  const F = o.length > 0 ? lead(lines[pos]!) : '';
  let ci = 0;
  const out: string[] = [];
  for (const it of n) {
    if (it.ctx) {
      out.push(ctxFile[ci++]!);
      continue;
    }
    let t = it.text;
    if (tier === 2 && t !== '' && !/^[ \t]+$/.test(t) && t.startsWith(P)) t = F + t.slice(P.length);
    out.push(t);
  }
  return out;
}

// ---------------------------------------------------------------------------
// Unified format (SPEC section 6).
// ---------------------------------------------------------------------------

interface HunkBodyLine {
  kind: ' ' | '-' | '+' | '\\';
  text: string;
  raw: string;
}

interface Hunk {
  a: number;
  body: HunkBodyLine[];
}

interface UniSection {
  oldPath: string | null;
  newPath: string | null;
  kind: 'create' | 'delete' | 'move' | 'change';
  hunks: Hunk[];
}

const HUNK_RE = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;
const DIFF_GIT_RE = /^diff --git a\/(\S+) b\/(\S+)$/;

function headerPath(line: string): string | null {
  // Text after the first four characters ('--- ' or '+++ '), up to the first
  // tab, with surrounding spaces removed; /dev/null means no file.
  let p = line.slice(4);
  const tab = p.indexOf('\t');
  if (tab >= 0) p = p.slice(0, tab);
  p = p.trim();
  if (p === '/dev/null') return null;
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
}

/** A `\` line follows the hunk's last context or `+` line. */
function hunkBackslash(hunk: Hunk): boolean {
  const body = hunk.body;
  let last = -1;
  for (let i = 0; i < body.length; i++) {
    if (body[i]!.kind === ' ' || body[i]!.kind === '+') last = i;
  }
  if (last < 0) return false;
  return body[last + 1] !== undefined && body[last + 1]!.kind === '\\';
}

/** A `\` line follows the section's last `+` line (creation case). */
function sectionBackslashAfterLastPlus(sec: UniSection): boolean {
  for (let h = sec.hunks.length - 1; h >= 0; h--) {
    const body = sec.hunks[h]!.body;
    let last = -1;
    for (let i = 0; i < body.length; i++) if (body[i]!.kind === '+') last = i;
    if (last >= 0) return body[last + 1] !== undefined && body[last + 1]!.kind === '\\';
  }
  return false;
}

/**
 * Apply the section's hunks in order to a file's lines. `d` is the running
 * sum of (N length - O length) over the hunks applied so far; a non-empty O
 * is taken at the occurrence nearest to A-1+d (ties go to the earlier one),
 * and an empty O inserts N after the first A+d lines.
 */
function applyHunks(st: FileState, hunks: Hunk[], strict: boolean, path: string): FileState {
  let lines = st.lines;
  let final = st.final;
  let d = 0;
  for (const hunk of hunks) {
    const oItems: OItem[] = [];
    const nItems: OItem[] = [];
    for (const b of hunk.body) {
      if (b.kind === ' ') {
        oItems.push({ text: b.text, ctx: true });
        nItems.push({ text: b.text, ctx: true });
      } else if (b.kind === '-') {
        oItems.push({ text: b.text, ctx: false });
      } else if (b.kind === '+') {
        nItems.push({ text: b.text, ctx: false });
      }
    }
    const oTexts = oItems.map((x) => x.text);
    if (oTexts.length === 0) {
      const at = Math.min(hunk.a + d, lines.length);
      const atEnd = at === lines.length;
      const ins = nItems.map((x) => x.text);
      lines = [...lines.slice(0, at), ...ins, ...lines.slice(at)];
      if (atEnd) final = !hunkBackslash(hunk);
    } else {
      const found = firstTier(lines, oTexts, strict);
      if (!found) throw new Fail('no-match', path);
      const target = hunk.a - 1 + d;
      let best = found.occ[0]!;
      for (const pos of found.occ) {
        if (Math.abs(pos - target) < Math.abs(best - target)) best = pos;
      }
      const pos = best;
      const runsToEnd = pos + oTexts.length === lines.length;
      const rep = applyO(lines, oItems, nItems, pos, found.tier);
      lines = [...lines.slice(0, pos), ...rep, ...lines.slice(pos + oTexts.length)];
      if (runsToEnd) final = !hunkBackslash(hunk);
    }
    d += nItems.length - oItems.length;
  }
  return { br: st.br, lines, final };
}

function parseUnified(lines: string[]): UniSection[] {
  const sections: UniSection[] = [];
  interface Builder {
    pairSeen: boolean;
    pairOld: string | null;
    pairNew: string | null;
    renameFrom: string | null;
    renameTo: string | null;
    diffOld: string | null;
    diffNew: string | null;
    newFile: boolean;
    deletedFile: boolean;
    hunks: Hunk[];
    hasHunk: boolean;
  }
  let sec: Builder | null = null;
  let cur: Hunk | null = null;

  const endBody = (): void => {
    if (cur && sec) {
      // Empty lines at the end of a body are not part of it.
      while (cur.body.length > 0 && cur.body[cur.body.length - 1]!.raw === '') cur.body.pop();
      sec.hunks.push(cur);
      cur = null;
    }
  };
  const endSection = (): void => {
    endBody();
    if (!sec) return;
    const oldPath = sec.pairSeen ? sec.pairOld : sec.renameFrom !== null ? sec.renameFrom : sec.diffOld;
    const newPath = sec.pairSeen ? sec.pairNew : sec.renameTo !== null ? sec.renameTo : sec.diffNew;
    let kind: UniSection['kind'];
    if (sec.newFile) kind = 'create';
    else if (sec.deletedFile) kind = 'delete';
    else if (oldPath === null) kind = 'create';
    else if (newPath === null) kind = 'delete';
    else if (oldPath !== newPath) kind = 'move';
    else kind = 'change';
    // A section naming no file at all is not an edit.
    if (oldPath === null && newPath === null) {
      sec = null;
      return;
    }
    sections.push({ oldPath, newPath, kind, hunks: sec.hunks });
    sec = null;
  };

  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (cur) {
      // Inside a hunk body. A --- line followed by a +++ line ends the
      // body and starts a new section; any other --- line is an old line.
      if (line.startsWith('--- ') && i + 1 < lines.length && lines[i + 1]!.startsWith('+++ ')) {
        endBody();
        continue;
      }
      if (line.startsWith(' ')) {
        cur.body.push({ kind: ' ', text: line.slice(1), raw: line });
        i++;
        continue;
      }
      if (line.startsWith('-')) {
        cur.body.push({ kind: '-', text: line.slice(1), raw: line });
        i++;
        continue;
      }
      if (line.startsWith('+')) {
        cur.body.push({ kind: '+', text: line.slice(1), raw: line });
        i++;
        continue;
      }
      if (line.startsWith('\\')) {
        cur.body.push({ kind: '\\', text: line.slice(1), raw: line });
        i++;
        continue;
      }
      if (line === '') {
        cur.body.push({ kind: ' ', text: '', raw: line });
        i++;
        continue;
      }
      // Any other line ends the body; reprocess it outside the body.
      endBody();
      continue;
    }

    if (line.startsWith('diff --git ')) {
      const m = DIFF_GIT_RE.exec(line);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      endSection();
      sec = {
        pairSeen: false,
        pairOld: null,
        pairNew: null,
        renameFrom: null,
        renameTo: null,
        diffOld: m[1]!,
        diffNew: m[2]!,
        newFile: false,
        deletedFile: false,
        hunks: [],
        hasHunk: false,
      };
      i++;
      continue;
    }

    if (line.startsWith('--- ')) {
      const next = i + 1 < lines.length ? lines[i + 1]! : '';
      if (next.startsWith('+++ ')) {
        // A ---/+++ pair: the section's own pair, or a new section.
        if (sec && sec.hasHunk) endSection();
        else if (sec && sec.pairSeen) endSection();
        if (!sec) {
          sec = {
            pairSeen: false,
            pairOld: null,
            pairNew: null,
            renameFrom: null,
            renameTo: null,
            diffOld: null,
            diffNew: null,
            newFile: false,
            deletedFile: false,
            hunks: [],
            hasHunk: false,
          };
        }
        sec.pairOld = headerPath(line);
        sec.pairNew = headerPath(next);
        sec.pairSeen = true;
        i += 2;
        continue;
      }
      // A --- line not followed by a +++ line.
      if (sec && !sec.hasHunk) throw new Exit2(`error: parse ${i + 2}`);
      i++;
      continue;
    }

    if (line.startsWith('@@')) {
      const m = HUNK_RE.exec(line);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      if (!sec) throw new Exit2(`error: parse ${i + 1}`);
      endBody();
      cur = { a: Number(m[1]), body: [] };
      sec.hasHunk = true;
      i++;
      continue;
    }

    if (sec && !sec.hasHunk) {
      // Header lines before the first hunk.
      if (line.startsWith('rename from ')) sec.renameFrom = line.slice('rename from '.length).trim();
      else if (line.startsWith('rename to ')) sec.renameTo = line.slice('rename to '.length).trim();
      else if (line.startsWith('new file mode')) sec.newFile = true;
      else if (line.startsWith('deleted file mode')) sec.deletedFile = true;
    }
    // Outside bodies, any other line is ignored (prose, code fences, ...).
    i++;
  }
  endSection();
  return sections;
}

function unifiedEdit(sec: UniSection, strict: boolean): Edit {
  return (tree) => {
    if (sec.kind === 'create') {
      const p = sec.newPath!;
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      const plus: string[] = [];
      for (const h of sec.hunks) for (const b of h.body) if (b.kind === '+') plus.push(b.text);
      const final = plus.length === 0 ? false : !sectionBackslashAfterLastPlus(sec);
      tree.now.set(p, plus.length === 0 ? '' : plus.join('\n') + (final ? '\n' : ''));
      return;
    }
    if (sec.kind === 'delete') {
      const p = sec.oldPath!;
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) === null) throw new Fail('missing', p);
      tree.now.set(p, null);
      return;
    }
    const oldP = sec.oldPath!;
    const newP = sec.newPath!;
    if (!safe(oldP)) throw new Fail('unsafe', oldP);
    if (sec.kind === 'move' && !safe(newP)) throw new Fail('unsafe', newP);
    const cur = tree.get(oldP);
    if (cur === null) throw new Fail('missing', oldP);
    if (sec.kind === 'move' && tree.get(newP) !== null) throw new Fail('exists', newP);
    const next = applyHunks(splitFile(cur), sec.hunks, strict, oldP);
    if (sec.kind === 'move') {
      tree.now.set(newP, joinFile(next));
      tree.now.set(oldP, null);
      tree.moves.push([oldP, newP]);
    } else {
      tree.now.set(oldP, joinFile(next));
    }
  };
}

// ---------------------------------------------------------------------------
// Search/replace format (SPEC section 7).
// ---------------------------------------------------------------------------

interface SrBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
}

function parseSearchReplace(lines: string[]): SrBlock[] {
  const blocks: SrBlock[] = [];
  let prevEnd = -1; // index just past the previous block's >>>>>>> REPLACE
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.replace(/[ \t]+$/, '') !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchLine = i + 1;
    // Path: the nearest line before SEARCH, after the previous block's end,
    // that is not blank and whose trimmed form does not start with ```.
    let path: string | null = null;
    for (let j = i - 1; j > prevEnd; j--) {
      const cand = lines[j]!;
      if (blank(cand)) continue;
      if (cand.trim().startsWith('```')) continue;
      path = cand.trim();
      break;
    }
    if (path === null) {
      if (blocks.length > 0) path = blocks[blocks.length - 1]!.path;
      else throw new Exit2(`error: parse ${searchLine}`);
    }
    // Find ======= then >>>>>>> REPLACE after SEARCH.
    let eq = -1;
    for (let j = i + 1; j < lines.length; j++) {
      if (lines[j]!.replace(/[ \t]+$/, '') === '=======') {
        eq = j;
        break;
      }
    }
    if (eq < 0) throw new Exit2(`error: parse ${searchLine}`);
    let end = -1;
    for (let j = eq + 1; j < lines.length; j++) {
      if (lines[j]!.replace(/[ \t]+$/, '') === '>>>>>>> REPLACE') {
        end = j;
        break;
      }
    }
    if (end < 0) throw new Exit2(`error: parse ${searchLine}`);
    blocks.push({
      path,
      oldLines: lines.slice(i + 1, eq),
      newLines: lines.slice(eq + 1, end),
    });
    prevEnd = end;
    i = end + 1;
  }
  return blocks;
}

function searchReplaceEdit(block: SrBlock, strict: boolean): Edit {
  return (tree) => {
    const p = block.path;
    if (!safe(p)) throw new Fail('unsafe', p);
    if (block.oldLines.length === 0) {
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, block.newLines.length === 0 ? '' : block.newLines.join('\n') + '\n');
      return;
    }
    const cur = tree.get(p);
    if (cur === null) throw new Fail('missing', p);
    const st = splitFile(cur);
    const found = firstTier(st.lines, block.oldLines, strict);
    if (!found) throw new Fail('no-match', p);
    if (found.occ.length > 1) throw new Fail('ambiguous', p);
    const pos = found.occ[0]!;
    const oItems: OItem[] = block.oldLines.map((t) => ({ text: t, ctx: false }));
    const nItems: OItem[] = block.newLines.map((t) => ({ text: t, ctx: false }));
    const rep = applyO(st.lines, oItems, nItems, pos, found.tier);
    const lines = [...st.lines.slice(0, pos), ...rep, ...st.lines.slice(pos + block.oldLines.length)];
    tree.now.set(p, joinFile({ br: st.br, lines, final: st.final }));
  };
}

// ---------------------------------------------------------------------------
// V4A format (SPEC section 8).
// ---------------------------------------------------------------------------

interface V4aChunk {
  anchor: string | null; // null = no anchor
  eof: boolean;
  body: HunkBodyLine[];
}

interface V4aSection {
  kind: 'add' | 'delete' | 'update';
  path: string;
  moveTo: string | null;
  lines: string[]; // add-file lines (without the leading '+')
  chunks: V4aChunk[];
}

function parseV4a(lines: string[]): V4aSection[] {
  // First non-blank line must be *** Begin Patch.
  let first = -1;
  for (let i = 0; i < lines.length; i++) {
    if (!blank(lines[i]!)) {
      first = i;
      break;
    }
  }
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  // Last non-blank line must be *** End Patch.
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (!blank(lines[i]!)) {
      last = i;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);

  const isSectionStart = (l: string): boolean =>
    l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');

  const sections: V4aSection[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) {
      i++;
      continue;
    }
    const secLine = i; // 0-based index of the *** Add/Delete/Update File line
    let sec: V4aSection | null = null;
    if (line.startsWith('*** Add File: ')) {
      sec = { kind: 'add', path: line.slice('*** Add File: '.length).trim(), moveTo: null, lines: [], chunks: [] };
    } else if (line.startsWith('*** Delete File: ')) {
      sec = { kind: 'delete', path: line.slice('*** Delete File: '.length).trim(), moveTo: null, lines: [], chunks: [] };
    } else if (line.startsWith('*** Update File: ')) {
      sec = { kind: 'update', path: line.slice('*** Update File: '.length).trim(), moveTo: null, lines: [], chunks: [] };
    } else {
      throw new Exit2(`error: parse ${i + 1}`);
    }
    sections.push(sec);
    i++;
    // The section's lines run to the next section start or *** End Patch.
    // Blank lines at the end of a section are not part of it.
    let end = i;
    while (end < last && !isSectionStart(lines[end]!) && lines[end]!.trim() !== '*** End Patch') end++;
    let bodyEnd = end;
    while (bodyEnd > i && blank(lines[bodyEnd - 1]!)) bodyEnd--;
    if (sec.kind === 'add') {
      for (let j = i; j < bodyEnd; j++) {
        const l = lines[j]!;
        if (l.startsWith('+')) sec.lines.push(l.slice(1));
        else if (l === '') sec.lines.push('');
        else throw new Exit2(`error: parse ${j + 1}`);
      }
      i = end;
      continue;
    }
    if (sec.kind === 'delete') {
      // A Delete section has no lines.
      if (bodyEnd > i) throw new Exit2(`error: parse ${i + 1}`);
      i = end;
      continue;
    }
    // Update: optional *** Move to: as the first line, then chunks.
    let j = i;
    if (j < bodyEnd && lines[j]!.startsWith('*** Move to: ')) {
      sec.moveTo = lines[j]!.slice('*** Move to: '.length).trim();
      j++;
    }
    let cur: V4aChunk | null = null;
    const endChunk = (): void => {
      if (cur) {
        sec!.chunks.push(cur);
        cur = null;
      }
    };
    while (j < bodyEnd) {
      const l = lines[j]!;
      if (l === '*** End of File') {
        if (cur) {
          cur.eof = true;
          endChunk();
        }
        j++;
        continue;
      }
      if (l.startsWith('*** ')) throw new Exit2(`error: parse ${j + 1}`);
      if (l.startsWith('@@')) {
        endChunk();
        const anchor = l.slice(2).trim();
        cur = { anchor: anchor === '' ? null : anchor, eof: false, body: [] };
        j++;
        continue;
      }
      if (!cur) cur = { anchor: null, eof: false, body: [] };
      if (l.startsWith(' ')) cur.body.push({ kind: ' ', text: l.slice(1), raw: l });
      else if (l.startsWith('-')) cur.body.push({ kind: '-', text: l.slice(1), raw: l });
      else if (l.startsWith('+')) cur.body.push({ kind: '+', text: l.slice(1), raw: l });
      else if (l === '') cur.body.push({ kind: ' ', text: '', raw: l });
      else throw new Exit2(`error: parse ${j + 1}`);
      j++;
    }
    endChunk();
    if (sec.chunks.length === 0 && sec.moveTo === null) {
      throw new Exit2(`error: parse ${secLine + 1}`);
    }
    i = end;
  }
  return sections;
}

function v4aEdit(sec: V4aSection, strict: boolean): Edit {
  return (tree) => {
    if (sec.kind === 'add') {
      if (!safe(sec.path)) throw new Fail('unsafe', sec.path);
      if (tree.get(sec.path) !== null) throw new Fail('exists', sec.path);
      tree.now.set(sec.path, sec.lines.length === 0 ? '' : sec.lines.join('\n') + '\n');
      return;
    }
    if (sec.kind === 'delete') {
      if (!safe(sec.path)) throw new Fail('unsafe', sec.path);
      if (tree.get(sec.path) === null) throw new Fail('missing', sec.path);
      tree.now.set(sec.path, null);
      return;
    }
    if (!safe(sec.path)) throw new Fail('unsafe', sec.path);
    if (sec.moveTo !== null && !safe(sec.moveTo)) throw new Fail('unsafe', sec.moveTo);
    const cur = tree.get(sec.path);
    if (cur === null) throw new Fail('missing', sec.path);
    if (sec.moveTo !== null && tree.get(sec.moveTo) !== null) throw new Fail('exists', sec.moveTo);
    const st = splitFile(cur);
    let lines = st.lines;
    let cursor = 0;
    for (const chunk of sec.chunks) {
      if (chunk.anchor !== null) {
        // First line at or after the cursor equal to the anchor, at the
        // first tier where one is (single line both sides).
        const found = firstTier(lines, [chunk.anchor], strict, cursor);
        if (!found) throw new Fail('no-match', sec.path);
        cursor = found.occ[0]! + 1;
      }
      const oItems: OItem[] = [];
      const nItems: OItem[] = [];
      for (const b of chunk.body) {
        if (b.kind === ' ') {
          oItems.push({ text: b.text, ctx: true });
          nItems.push({ text: b.text, ctx: true });
        } else if (b.kind === '-') {
          oItems.push({ text: b.text, ctx: false });
        } else if (b.kind === '+') {
          nItems.push({ text: b.text, ctx: false });
        }
      }
      const oTexts = oItems.map((x) => x.text);
      if (oTexts.length === 0) {
        const at = chunk.eof ? lines.length : cursor;
        const ins = nItems.map((x) => x.text);
        lines = [...lines.slice(0, at), ...ins, ...lines.slice(at)];
        cursor = at + ins.length;
        continue;
      }
      if (chunk.eof) {
        // Only an occurrence ending at the file's last line.
        const found = firstTier(lines, oTexts, strict, cursor);
        if (!found) throw new Fail('no-match', sec.path);
        const ends = found.occ.filter((pos) => pos + oTexts.length === lines.length);
        if (ends.length === 0) throw new Fail('no-match', sec.path);
        const pos = ends[0]!;
        const rep = applyO(lines, oItems, nItems, pos, found.tier);
        lines = [...lines.slice(0, pos), ...rep, ...lines.slice(pos + oTexts.length)];
        cursor = pos + rep.length;
      } else {
        const found = firstTier(lines, oTexts, strict, cursor);
        if (!found) throw new Fail('no-match', sec.path);
        const pos = found.occ[0]!;
        const rep = applyO(lines, oItems, nItems, pos, found.tier);
        lines = [...lines.slice(0, pos), ...rep, ...lines.slice(pos + oTexts.length)];
        cursor = pos + rep.length;
      }
    }
    const out = joinFile({ br: st.br, lines, final: st.final });
    if (sec.moveTo !== null) {
      tree.now.set(sec.moveTo, out);
      tree.now.set(sec.path, null);
      tree.moves.push([sec.path, sec.moveTo]);
    } else {
      tree.now.set(sec.path, out);
    }
  };
}

// ---------------------------------------------------------------------------
// JSON format (SPEC section 9).
// ---------------------------------------------------------------------------

type Edit = (tree: Tree) => void;

function countOccurrences(text: string, needle: string): number {
  let count = 0;
  let from = 0;
  while (true) {
    const at = text.indexOf(needle, from);
    if (at < 0) return count;
    count++;
    from = at + 1;
  }
}

function jsonEdit(item: unknown, line: number): Edit {
  if (typeof item !== 'object' || item === null || Array.isArray(item)) {
    throw new Exit2(`error: parse ${line}`);
  }
  const rec = item as Record<string, unknown>;
  const path = rec['path'];
  const command = rec['command'];
  if (typeof path !== 'string' || typeof command !== 'string') {
    throw new Exit2(`error: parse ${line}`);
  }
  if (command === 'create') {
    const fileText = rec['file_text'];
    if (typeof fileText !== 'string') throw new Exit2(`error: parse ${line}`);
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, fileText);
    };
  }
  if (command === 'str_replace') {
    const oldStr = rec['old_str'];
    const newStr = rec['new_str'];
    if (typeof oldStr !== 'string' || oldStr === '') throw new Exit2(`error: parse ${line}`);
    if (newStr !== undefined && typeof newStr !== 'string') throw new Exit2(`error: parse ${line}`);
    const replacement = newStr === undefined ? '' : newStr;
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      const cur = tree.get(path);
      if (cur === null) throw new Fail('missing', path);
      const state = splitFile(cur);
      const text = state.lines.join('\n');
      const found = countOccurrences(text, oldStr);
      if (found === 0) throw new Fail('no-match', path);
      if (found > 1) throw new Fail('ambiguous', path);
      // A function replacer keeps `$` sequences in new_str literal.
      const replaced = text.replace(oldStr, () => replacement);
      const next: FileState =
        replaced === ''
          ? { br: state.br, lines: [], final: false }
          : { br: state.br, lines: replaced.split('\n'), final: state.final };
      tree.now.set(path, joinFile(next));
    };
  }
  if (command === 'insert') {
    const insertLine = rec['insert_line'];
    const newStr = rec['new_str'];
    if (typeof insertLine !== 'number' || !Number.isInteger(insertLine)) {
      throw new Exit2(`error: parse ${line}`);
    }
    if (typeof newStr !== 'string') throw new Exit2(`error: parse ${line}`);
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      const cur = tree.get(path);
      if (cur === null) throw new Fail('missing', path);
      const state = splitFile(cur);
      if (insertLine < 0 || insertLine > state.lines.length) throw new Fail('no-match', path);
      const lines = patchLines(newStr);
      const next = [...state.lines.slice(0, insertLine), ...lines, ...state.lines.slice(insertLine)];
      tree.now.set(path, joinFile({ br: state.br, lines: next, final: state.final }));
    };
  }
  throw new Exit2(`error: parse ${line}`);
}

function parseJson(lines: string[]): Edit[] {
  if (lines.length === 0) return [];
  const first = lines[0]!;
  if (first.trim().startsWith('[')) {
    try {
      const parsed: unknown = JSON.parse(lines.join('\n'));
      if (!Array.isArray(parsed)) throw new Error('not an array');
      return parsed.map((item) => jsonEdit(item, 1));
    } catch {
      throw new Exit2('error: parse 1');
    }
  }
  const edits: Edit[] = [];
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]!;
    if (blank(line)) continue;
    try {
      edits.push(jsonEdit(JSON.parse(line), i + 1));
    } catch {
      throw new Exit2(`error: parse ${i + 1}`);
    }
  }
  return edits;
}

// ---------------------------------------------------------------------------
// Working tree, patch reading, CLI parsing, and the run loop (SPEC 1-4, 10).
// ---------------------------------------------------------------------------

class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: Array<[string, string]> = [];

  original(p: string): string | null {
    if (this.orig.has(p)) return this.orig.get(p)!;
    let value: string | null;
    try {
      const st = statSync(p);
      if (!st.isFile()) value = null;
      else value = readFileSync(p, 'utf8');
    } catch {
      value = null;
    }
    this.orig.set(p, value);
    return value;
  }

  get(p: string): string | null {
    if (this.now.has(p)) return this.now.get(p)!;
    return this.original(p);
  }
}

function readPatch(patch: string | null): string {
  if (patch === null || patch === '-') {
    return readFileSync(0, 'utf8');
  }
  try {
    return readFileSync(patch, 'utf8');
  } catch {
    throw new Exit2('error: no-patch');
  }
}

function detectFormat(lines: string[]): 'unified' | 'search-replace' | 'v4a' | 'json' {
  let first = -1;
  for (let i = 0; i < lines.length; i++) {
    if (!blank(lines[i]!)) {
      first = i;
      break;
    }
  }
  if (first < 0) throw new Exit2('error: format');
  const firstText = lines[first]!;
  if (firstText.trim() === '*** Begin Patch') return 'v4a';
  const firstChar = firstText.trimStart().charAt(0);
  if (firstChar === '[' || firstChar === '{') return 'json';
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i]!;
    if (l.replace(/[ \t]+$/, '') === '<<<<<<< SEARCH') return 'search-replace';
    if (l.startsWith('diff --git ')) return 'unified';
    if (l.startsWith('--- ') && i + 1 < lines.length && lines[i + 1]!.startsWith('+++ ')) {
      return 'unified';
    }
  }
  throw new Exit2('error: format');
}

interface Cli {
  format: string;
  check: boolean;
  strict: boolean;
  patch: string | null;
}

function parseCli(argv: string[]): Cli {
  let format = 'auto';
  let check = false;
  let strict = false;
  let patch: string | null = null;
  let positional = 0;
  let afterDashDash = false;
  for (const arg of argv) {
    if (!afterDashDash && arg === '--') {
      afterDashDash = true;
      continue;
    }
    if (!afterDashDash && arg.startsWith('-') && arg !== '-') {
      if (arg === '--check') {
        if (check) throw new Exit2('error: usage');
        check = true;
        continue;
      }
      if (arg === '--strict') {
        if (strict) throw new Exit2('error: usage');
        strict = true;
        continue;
      }
      if (arg.startsWith('--format=')) {
        const value = arg.slice('--format='.length);
        if (format !== 'auto' || !FORMATS.includes(value)) throw new Exit2('error: usage');
        format = value;
        continue;
      }
      throw new Exit2('error: usage');
    }
    positional++;
    if (positional > 1) throw new Exit2('error: usage');
    patch = arg;
  }
  return { format, check, strict, patch };
}

function run(argv: string[]): number {
  let cli: Cli;
  try {
    cli = parseCli(argv);
  } catch (e) {
    if (e instanceof Exit2) {
      writeSync(1, `${e.line}\n`);
      return 2;
    }
    throw e;
  }
  const text = (() => {
    try {
      return readPatch(cli.patch);
    } catch (e) {
      if (e instanceof Exit2) {
        writeSync(1, `${e.line}\n`);
        return null;
      }
      throw e;
    }
  })();
  if (text === null) return 2;
  const lines = patchLines(text);
  let edits: Edit[];
  try {
    const kind = cli.format === 'auto' ? detectFormat(lines) : cli.format;
    if (kind === 'unified') edits = parseUnified(lines).map((s) => unifiedEdit(s, cli.strict));
    else if (kind === 'search-replace') edits = parseSearchReplace(lines).map((b) => searchReplaceEdit(b, cli.strict));
    else if (kind === 'v4a') edits = parseV4a(lines).map((s) => v4aEdit(s, cli.strict));
    else edits = parseJson(lines);
  } catch (e) {
    if (e instanceof Exit2) {
      writeSync(1, `${e.line}\n`);
      return 2;
    }
    throw e;
  }

  const tree = new Tree();
  const failures: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesBefore = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (e instanceof Fail) {
        tree.now.clear();
        for (const [k, v] of before) tree.now.set(k, v);
        tree.moves.length = movesBefore;
        failures.push(e);
        continue;
      }
      throw e;
    }
  }

  const out: string[] = [];
  if (failures.length > 0) {
    for (const f of failures) out.push(`error: ${f.code} ${f.path}`);
    out.push(`failed: ${failures.length} of ${edits.length} edits`);
    writeSync(1, out.map((l) => `${l}\n`).join(''));
    return 1;
  }

  // Change lines in UTF-8 byte order; a move (old deleted + new created,
  // where old existed before and new did not) collapses to one R line
  // sorted by the new path.
  const changed: string[] = [];
  for (const [p, v] of tree.now) {
    if (tree.original(p) !== v) changed.push(p);
  }
  const movedNew = new Map<string, string>();
  const movedOld = new Map<string, string>();
  for (const [oldP, newP] of tree.moves) {
    // A move qualifies only when the old path is deleted in the final tree
    // and the new path is created there (old existed before, new did not).
    if (
      tree.original(oldP) !== null &&
      tree.get(oldP) === null &&
      tree.original(newP) === null &&
      tree.get(newP) !== null
    ) {
      movedNew.set(newP, oldP);
      movedOld.set(oldP, newP);
    }
  }
  const byteOrder = (a: string, b: string): number =>
    Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));
  const sorted = [...changed].sort(byteOrder);
  const printed = new Set<string>();
  for (const p of sorted) {
    if (printed.has(p)) continue;
    if (movedOld.has(p)) {
      // The old half of a move: defer to the R line at the new path.
      const newP = movedOld.get(p)!;
      if (changed.includes(newP) && !printed.has(newP)) continue;
    }
    if (movedNew.has(p)) {
      const oldP = movedNew.get(p)!;
      if (changed.includes(oldP) && !printed.has(oldP)) {
        out.push(`R ${oldP} -> ${p}`);
        printed.add(oldP);
        printed.add(p);
        continue;
      }
    }
    const v = tree.now.get(p)!;
    const before = tree.original(p);
    if (before === null) out.push(`A ${p}`);
    else if (v === null) out.push(`D ${p}`);
    else out.push(`M ${p}`);
    printed.add(p);
  }
  const n = out.length;
  out.push(`ok: ${n} file${n === 1 ? '' : 's'}`);
  writeSync(1, out.map((l) => `${l}\n`).join(''));
  if (!cli.check) {
    for (const [p, v] of tree.now) {
      if (tree.original(p) === v) continue;
      if (v === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, v, 'utf8');
      }
    }
  }
  return 0;
}

const code = run(process.argv.slice(2));
process.exit(code);
