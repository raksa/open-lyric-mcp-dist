# open-lyric-mcp — how to use the MCP server

`open-lyric-mcp` is a [Model Context Protocol](https://modelcontextprotocol.io)
server for songs written in the **Open Lyric** notation (Markdown with
` ```ol:<Section> ` fences — see `schema.md` in the `open-lyric` package). It
runs the Open Lyric editor's own validator, parser, transposer, renderers and
exporters in Node, so an AI client can read, check, change and export songs
exactly the way the editor would.

Language plugins are not part of it: no Khmer keyboard, spellcheck or fonts.

## Install

Requires Node.js 20 or newer. Nothing to install up front — clients start it
with `npx`:

```bash
npx -y open-lyric-mcp --help
```

### Claude Code

```bash
claude mcp add open-lyric -- npx -y open-lyric-mcp
# every project: claude mcp add --scope user open-lyric -- npx -y open-lyric-mcp
```

### Claude Desktop

`claude_desktop_config.json` (Settings → Developer → Edit Config):

```json
{
  "mcpServers": {
    "open-lyric": {
      "command": "npx",
      "args": ["-y", "open-lyric-mcp", "--root", "/Users/me/Songs"]
    }
  }
}
```

Give a `--root`: a desktop app's working directory is not a song folder.

### Cursor

`~/.cursor/mcp.json`, or `.cursor/mcp.json` in a project:

```json
{
  "mcpServers": {
    "open-lyric": { "command": "npx", "args": ["-y", "open-lyric-mcp"] }
  }
}
```

### VS Code

Install the **Open Lyric MCP** extension (it registers the server, bundled, in
the MCP Servers list), or add it to `.vscode/mcp.json`:

```json
{
  "servers": {
    "open-lyric": { "type": "stdio", "command": "npx", "args": ["-y", "open-lyric-mcp"] }
  }
}
```

On Windows, a client that cannot start `npx` directly takes
`"command": "cmd", "args": ["/c", "npx", "-y", "open-lyric-mcp"]`.

## Command line

```text
open-lyric-mcp [--http] [--port <n>] [--host <host>] [--root <dir>]… [--read-only]
```

| Option | Environment | Meaning |
| --- | --- | --- |
| *(none)* | | Serve MCP over stdio — what every client above uses. |
| `--http` | | Serve stateless Streamable HTTP instead: `POST /mcp`. Other paths answer 404, other methods 405. |
| `--port <n>` | `OPEN_LYRIC_MCP_PORT` | HTTP port. Default `3333`. |
| `--host <host>` | | HTTP interface. Default `127.0.0.1`. |
| `--root <dir>` (repeatable) | `OPEN_LYRIC_MCP_ROOTS` (a path list: `:`-separated, `;` on Windows) | Folders the file tools may use. |
| `--read-only` | `OPEN_LYRIC_MCP_READ_ONLY=1` (`1`/`true`/`yes`/`on`) | Never write a file. |
| `-v`, `--version` / `-h`, `--help` | | Print and exit. |

A bad option exits with code 2. stdout carries only the protocol; logging goes
to stderr.

Over HTTP on a loopback host the server checks the `Host` header (DNS-rebinding
protection). There is **no authentication**: binding `--host 0.0.0.0` hands
the file tools to anyone who can reach the port.

## Files and roots

Tools that take a `path` work only inside the **allowed roots**:

1. the roots the client announces (MCP `roots/list`, re-read when the client
   says they changed), plus
2. every `--root` / `OPEN_LYRIC_MCP_ROOTS` folder;
3. with neither, the server's working directory.

A relative path resolves against the first root. Every path is checked after
resolving symlinks, so a link pointing outside the roots is refused, for
reading and writing alike. Song files are written only as `.md`/`.markdown`
(`*.ol.md` is the convention); exports only with their format's extension.
Missing folders are created. An existing file is replaced only when the call
says `overwrite: true` (edit tools rewrite the file they were given).

**Read-only mode** (`--read-only`): `write_song` is not offered at all; an edit
tool given a `path` returns the new text with `written: false` and a note; an
export with `outputPath` is refused.

## How tools take a song

Every tool that reads a song accepts **`text`** (the notation itself) **or
`path`** (a song file inside the roots).

Edit tools (`transpose_song`, `set_config_field`, `add_section`,
`rename_section`, `delete_section`, `set_section_lines`, `format_song`,
`apply_fixes`):

- given `text`, they return the new `text`;
- given `path`, they write the file in place and return `path` and
  `written: true` — or, with `dryRun: true`, return the new `text` without
  writing. An edit that changes nothing writes nothing (`note: "No change."`);
- every result carries `validation` — `{ valid, errorCount, warningCount,
  diagnostics[] }`, each diagnostic with `message`, `severity`
  (`error` / `warning` / `information` / `hint`) and 1-based `line`, `column`,
  `endLine`, `endColumn` (just past the last character). A diagnostic whose
  fix is known also has `fix: { title, text }`: put `text` in place of that
  range — `"Verse 2"` for a header written `ol:Vers 2`, `"[G]"` for `[Gzz]`.
  `apply_fixes` does that for every such diagnostic at once.

Creating tools (`create_song`, `song_from_json`, `import_plain_text`) return
the notation, or write it to `path` (refusing an existing file unless
`overwrite`).

A tool that fails returns an MCP error result (`isError: true`) whose text says
why — an unknown section, a file outside the roots, an invalid key.

## Tools

### Analyse (read-only)

| Tool | What it returns |
| --- | --- |
| `validate_song` | Every diagnostic, from the editor's validator. |
| `parse_song` | The song object `{ config, sections }` (schema: `open-lyric://schema/song.schema.json`) plus the Markdown `preamble` outside the fences. |
| `get_song_info` | Title and metadata, Structure step by step (with undeclared and unused parts), the sections, every chord, attachments, strumming patterns. |
| `list_sections` | Each section fence in written order: part name, type, line range, whether Structure plays it. |
| `get_section` | One section's body lines (`section`: its part name, e.g. `Verse 1`). |
| `explain_structure` | A Structure value read step by step (`structure`, optionally with the song to check it against). |
| `list_chords` | Every distinct chord: name, simplified triad, degree hints, diatonic or not. |

### Music theory

| Tool | |
| --- | --- |
| `transpose_song` | Rewrites every `[Chord]` and progression chord and the Config `Key`. `toKey` (same mode as the song — a mode change is refused) or `semitones`. |
| `transpose_chord` | One chord by `semitones`, or `fromKey` → `toKey`, spelled the way the target key spells it. |
| `get_key_chords` | A key's diatonic triads, and the keys Config accepts. |
| `describe_chord` | Is the symbol valid Open Lyric, its name and simplified triad, and fingerings on `guitar` or `ukulele` (easiest first; `limit`). |

### Author and edit

| Tool | |
| --- | --- |
| `create_song` | A new valid song from fields (`title` required; `key`, `tempo` — `72` becomes `72bpm` —, `time`, `locales`, `keywords`, `year`, `melody`, `attachments`, `strummingPatterns`, …) and `sections`. Structure defaults to every section once, in order, adjacent repeats merged (`Cx2`). |
| `song_from_json` | A song object → notation, validated. |
| `import_plain_text` | Plain text in Open Lyric's own text layout (what `render_song` `text` produces: title/artist lines, a `Key: G, Tempo: 68bpm, Time: 4/4` line, `Section:` headings, indented chord/lyric lines) → notation. Unknown section labels are mapped and reported. |
| `set_config_field` | Set, replace, or (empty `value`) remove one Config field; a new field goes in canonical order. Title and Structure cannot be removed. |
| `add_section` | A new fence after the last one. Numbered types take the next free number unless `index` is given; its code is appended to Structure unless `appendToStructure: false`. |
| `rename_section` | Rename, renumber or retype a section; every Structure step that plays it follows. |
| `delete_section` | Remove a fence and every Structure step that plays it. |
| `set_section_lines` | Replace a section's whole body. |
| `format_song` | The editor's Format Document as it runs with no language plugin: repeated invisible characters collapsed, trailing whitespace trimmed. A language's word-separator repair comes from its editor plugin, and none runs here: Khmer's (the km-KH plugin turns a space typed between Khmer letters into U+200B) is `fix_khmer` with `rules: ['word-separator']` on the Khmer Lint MCP server. When the song's `Locales` include Khmer (`km`, `km-KH`), the result carries a `hint` saying so. |
| `apply_fixes` | Applies the `fix` of every diagnostic that has one — a near-miss fence header, a Config field name or value, a chord annotation, a repeat mark — then validates again and repeats while fixes are left (correcting a header can clear the Structure error it caused; at most 10 rounds; overlapping fixes wait for the next round). `applied` lists each fix made (`message`, `title`, and the 1-based `line` and `column` it was at); diagnostics with no known fix stay in `validation`. |

### Render and export

`render_song` `format`:

- `text` — the plain-text song: title, meta line, structure, sections in
  performance order. A chord row sits over its lyric by on-screen column:
  marks drawn on a letter (Khmer vowel signs, a Khmer subscript consonant)
  and invisible characters take no column, so chords stay over their
  syllables in a monospace font, and `import_plain_text` reads them back to
  the same place;
- `lyric-html` — the lyric view's HTML fragment;
- `markdown-html` — the whole document, fences as cards;
- `html-document` — a standalone page with the stylesheet inlined (`view`:
  `lyric` | `markdown`; `theme`: `light` | `dark`). Large: to keep one, export
  it.

All HTML is static: the editor's in-place editing controls are removed, and
what the editor makes clickable (chords, tempo, a pattern reference) is plain
text.

`export_song` `format`: `docx` (Word, from the markdown view), `pptx` (text
slides: a title slide, then each section in performance order, then the song
notes the Structure leaves out; `theme`, default `dark`), `slideshow` (that
same deck as one self-contained `.html` slide show page, the kind the editor's
"Download as HTML" writes: slide and grid views with the notes, a full-screen
show playing each slide's transition, and a presenter view with the next
slide, a timer and an audience window, the display kept from sleeping while
either is up, and each slide's words announced to screen readers; it runs offline in any browser with
JavaScript; `theme` as for `pptx`; its text is set in the fonts the viewing
computer has unless `fontFile` carries one (below), and the viewer's own words
are English), `html` (`theme` default `light`), `txt`, `json` (the song object) or
`md` (the notation). With `outputPath` the file is written inside the roots;
without it the file comes back as an embedded resource (base64 `blob` for
docx/pptx, `text` for the rest). A `slideshow` page is about 100 KB, mostly
its viewer: to keep one, give `outputPath`.

The `pptx` and `slideshow` decks are lyrics only unless `hideChords` is
`false`: chords, and lines that are only a chord progression, are left out,
including a progression led by a `{p:}` or `{c:}` cue (which `hideChords`
keeps in the other formats). Notation directives (`{p: #1}`, `{c: …}`) never
reach a slide, and a line that held nothing else is left out. Each lyric slide has the song's title,
the section's name, and the lyrics in a box. These options lay the deck out
(the other formats ignore them, except `fontFace`, below):

| Option            | Values                                                | Default                                                     |
| ----------------- | ----------------------------------------------------- | ----------------------------------------------------------- |
| `linesPerSlide`   | 1 to 8. A lyric line and its chord row stay together. | 8                                                           |
| `fontFace`        | Any font name, for the titles and the lyrics.         | Arial, and Courier New for the lyrics when chords are shown |
| `fontSize`        | The lyrics' size in points, 12 to 96.                 | 24                                                          |
| `textAlign`       | `left`, `center`, `right`                             | `left`                                                      |
| `transition`      | `none`, or a transition such as `fade`, `push`, `morph` | `none`                                                    |
| `transitionSpeed` | `slow`, `medium`, `fast`                              | `medium`                                                    |

- `fontFace` is named in the file, so pick one with glyphs for the song's
  script — and, without `fontFile`, one the screen's computer has. Chord rows
  are spaced in columns, so with chords shown keep a monospace face and
  `left`.
- `fontFace` is the one deck option the other formats take too: `docx` sets
  every run in it (default Calibri), and `html` names it ahead of the page's
  system font stack (`system-ui`, …, `Noto Sans Khmer`, `sans-serif`), so a
  reader without it still gets readable text. On its own it is only named:
  `fontFace: "Battambang"` for a Khmer song shows Battambang where it is
  installed.
- `fontFile` carries the face too, so the text reads in it on a computer
  without it: a path inside the roots to a TrueType font (`.ttf`, its first
  bytes `0x00010000` or `true`; at most 4 MB, refused before it is read),
  for `docx`, `slideshow` and `html` only. It needs `fontFace`, the family
  name the font calls itself, which every run or rule still names. `docx`
  embeds it as Word does (`word/fonts/font1.odttf`, its first 32 bytes
  obfuscated, listed under `<w:embedRegular>` in the font table with its key
  in capitals); `slideshow` and `html` declare it in one `@font-face`
  rule with the file written into the page as a `data:` URL, which makes the
  page that much larger. One file is one face: bold and italic text is drawn
  from it by the reader. A font whose `OS/2` `fsType` forbids embedding
  (restricted, or bitmap-only) is refused, as are OpenType-CFF (`.otf`), WOFF
  and WOFF2 files, and `fontFile` with `pptx`, `txt`, `json` or `md`. The
  error says which.
- The lyrics' box is marked shrink-to-fit (`normAutofit`): PowerPoint draws
  text that overflows it smaller when it opens the deck, and so does the
  slide show page. A viewer that ignores the mark lets many lines at a large
  size run over the box.
- `transition` takes the 57 PowerPoint transitions the editor's Presentation
  dialog lists (the tool's schema enumerates them), each in its default
  direction. The slide show page plays it too.
- A value out of range is refused with the reason, such as
  `linesPerSlide must be a whole number from 1 to 8.` or `Unknown transition
  "sparkle". Use one of: none, morph, fade, …`.

View options, for both: `key` (render transposed), `simplifyChords`,
`hideChords`, `hideLeadingBars`, `hideStrummingPatterns`, `hideAttachments`,
`showComments`, `hideNotes`, `section` (one part only — not for
`markdown-html`). An `ol:Note` the Structure leaves out follows the song,
after its sections. `hideNotes` leaves such notes out; a note the Structure
names stays in its place either way.

### Files

| Tool | |
| --- | --- |
| `list_songs` | `*.ol.md` files under the roots, or one `directory` inside them (`recursive`, default on; `includeAllMarkdown` for every `.md`). Skips dot-folders, `node_modules` and `dist`; at most 500. |
| `read_song` | A song file and its validation. |
| `write_song` | Validates, then writes. An invalid song is refused unless `allowInvalid`; an existing file is replaced only with `overwrite`. Absent in read-only mode. |

### Reference

`list_examples` / `get_example` (the bundled example songs, by id or file
name), `get_notation_reference` (the whole notation reference, or one numbered
`section`), `list_fence_types`, `get_config_fields`.

Every tool declares an output schema and returns `structuredContent`, plus the
same data as text for clients that read only text.

## Resources

| URI | Content |
| --- | --- |
| `open-lyric://docs/notation` | The notation reference (Markdown). |
| `open-lyric://docs/notation/{section}` | One numbered section of it, `1`–`8`. |
| `open-lyric://schema/grammar.json` | Every fence, pattern, enum and diagnostic, as data. |
| `open-lyric://schema/song.schema.json` | JSON Schema of the song object. |
| `open-lyric://examples` | The example list. |
| `open-lyric://examples/{id}` | One example's notation (ids complete). |
| `open-lyric://reference/fences` | Section types, Structure codes, body rules. |
| `open-lyric://reference/config-fields` | Config fields and their value sets. |

## Prompts

| Prompt | Arguments |
| --- | --- |
| `write_song` | `topic`; optional `key`, `style`, `language` |
| `convert_chord_sheet` | `chordSheet` (chords over lyrics, ChordPro, …) |
| `fix_song` | `text` or `path` — the current diagnostics are inlined; it starts the client on `apply_fixes` |
| `add_translation` | `text` or `path`, `language` |
| `review_song` | `text` or `path` |
| `arrange_song` | `text` or `path`; optional `goal` |

## Use it from code

```js
import { readFile } from 'node:fs/promises';
import {
  createOpenLyricMcpServer,
  operations,
  runHttpServer,
  runStdioServer,
} from 'open-lyric-mcp';

// The plain functions behind the tools — no MCP involved.
const { valid, diagnostics } = operations.validateSong(markdown);
const { text } = operations.transposeSong(markdown, { toKey: 'A' });
const { text: fixed, applied } = operations.applyFixes(markdown); // apply_fixes
const docx = await operations.exportSong(markdown, { format: 'docx' }); // { data: Uint8Array, fileName, mimeType }
const show = await operations.exportSong(markdown, { format: 'slideshow' }); // data: the .html page, a string
const carried = await operations.exportSong(markdown, {
  format: 'docx',
  fontFace: 'Battambang',
  fontData: await readFile('Battambang-Regular.ttf'), // any Uint8Array: export_song's fontFile, read by you
});
const deck = await operations.exportSong(markdown, {
  format: 'pptx',
  linesPerSlide: 2,
  textAlign: 'center',
  transition: 'fade',
}); // the deck options, as export_song takes them

// Your own transport: any SDK transport connects to the server.
await runStdioServer(createOpenLyricMcpServer({ roots: ['/srv/songs'], readOnly: true }));
const http = await runHttpServer(() => createOpenLyricMcpServer(), { port: 4000 });
// http.url, await http.close()
```

`createOpenLyricMcpServer(options)`: `roots`, `readOnly`, `cwd` (base for
relative roots, and the fallback root), `listClientRoots` (replace the roots
lookup). `version` is the package version.

The package is ESM-only. Importing it installs a minimal DOM (linkedom) on
`globalThis` when there is none — the Open Lyric core needs one to load — so
do not import it into a process that owns a different global DOM.
