# Open Lyric MCP

A [Model Context Protocol](https://modelcontextprotocol.io) server for songs
written in the [Open Lyric](https://github.com/raksa/open-lyric-dist#readme)
notation. It runs the Open Lyric editor's own validator, transposer, renderers
and exporters in Node, so an AI client can validate, analyze, transpose, edit,
render and export songs — DOCX and PowerPoint included — the way the editor
would.

## Install

Node.js 20 or newer. Clients start it with `npx`:

```bash
# Claude Code
claude mcp add open-lyric -- npx -y open-lyric-mcp
```

```jsonc
// Claude Desktop (claude_desktop_config.json), Cursor (~/.cursor/mcp.json)
{
  "mcpServers": {
    "open-lyric": { "command": "npx", "args": ["-y", "open-lyric-mcp", "--root", "/path/to/songs"] }
  }
}
```

```jsonc
// VS Code (.vscode/mcp.json) — or install the "Open Lyric MCP" extension
{
  "servers": {
    "open-lyric": { "type": "stdio", "command": "npx", "args": ["-y", "open-lyric-mcp"] }
  }
}
```

## What it offers

- **30 tools** — validate, parse to JSON, summarize, list sections and chords,
  explain Structure; transpose a song or a chord, a key's chords, chord
  fingerings (guitar, ukulele); create a song, import plain text or a song
  object, set Config fields, add/rename/delete sections (Structure kept in
  step); render as text or HTML; export DOCX, PPTX, HTML, TXT, JSON or
  Markdown; list, read and write song files; the examples and the notation
  reference.
- **Resources** — the notation reference (whole or by section), the grammar
  and the song-object JSON Schema, the example songs, section types, Config
  fields.
- **Prompts** — write a song, convert a chord sheet, fix validation errors,
  add a translation, review, arrange.

Every edit returns the song's validation. File tools stay inside the roots the
client announces, plus `--root` folders (else the working directory);
`--read-only` never writes. `--http` serves Streamable HTTP on
`127.0.0.1:3333/mcp` instead of stdio.

The full guide — every tool, option, resource and rule — is
[`how-to_open-lyric-mcp.md`](./how-to_open-lyric-mcp.md), shipped in this
package.

## Use it from code

```js
import { createOpenLyricMcpServer, operations, runStdioServer } from 'open-lyric-mcp';

operations.validateSong(markdown); // { valid, errorCount, warningCount, diagnostics }
await runStdioServer(createOpenLyricMcpServer({ roots: ['/srv/songs'] }));
```

ESM only. Importing the package installs a minimal DOM (linkedom) on
`globalThis` when none exists, which the Open Lyric core needs to load.

## Build

From the repo root: `npm run pack -- open-lyric-mcp`. The server bundles the
Open Lyric sources it uses (they need Vite for their `?raw`/`?inline`
imports); the npm modules in `dependencies` stay external.

### Releasing

For maintainers: bump `version` in `package.json`, `npm run pack -- open-lyric-mcp`
(this also syncs `server.json`), then `npm run pub -- open-lyric-mcp`. To list
the release in the MCP Registry, run `mcp-publisher login github` and
`mcp-publisher publish` in this folder — the registry checks this package's
`mcpName` against `server.json`'s `name`.

## License

MIT
