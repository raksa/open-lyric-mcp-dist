/**
 * `open-lyric-mcp` — an MCP server for the Open Lyric song notation.
 *
 * The command line (`npx open-lyric-mcp`) is the usual way in; this module is
 * for hosts that embed the server: create it, then connect any MCP transport —
 * `runStdioServer` / `runHttpServer` here, or the SDK's own. `operations` are
 * the plain functions the tools wrap, for Node callers that want them without
 * MCP.
 *
 * Importing it installs a minimal DOM (linkedom) on `globalThis` when there is
 * none — the Open Lyric core needs one to load. Don't import it into a process
 * that owns a different global DOM.
 */
export { createOpenLyricMcpServer, OPEN_LYRIC_MCP_INSTRUCTIONS, } from '../../../src/open-lyric-mcp/server.js';
export type { OpenLyricMcpServerOptions } from '../../../src/open-lyric-mcp/server.js';
export { runHttpServer, runStdioServer, } from '../../../src/mcp-common/transports.js';
export type { HttpServerOptions, RunningHttpServer, } from '../../../src/mcp-common/transports.js';
export * as operations from '../../../src/open-lyric-mcp/operations/index.js';
export { OPEN_LYRIC_MCP_VERSION as version } from '../../../src/open-lyric-mcp/version.js';
