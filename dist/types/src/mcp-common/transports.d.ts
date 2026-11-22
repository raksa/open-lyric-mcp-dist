import { type McpServer } from '@modelcontextprotocol/sdk/server/mcp.js';
/**
 * The two ways the Open Lyric MCP servers are reached: stdio (one client, the
 * process that started the server — what `npx`-launched servers use) and
 * Streamable HTTP (any number of clients on a port).
 *
 * The HTTP server is stateless: every POST gets a fresh `McpServer` and
 * transport, so no session state is kept between requests. It listens on
 * loopback by default and turns on the SDK's DNS-rebinding protection for
 * loopback hosts.
 */
export declare function runStdioServer(server: McpServer): Promise<void>;
export interface HttpServerOptions {
    port?: number;
    host?: string;
    /** URL path of the endpoint. Default `/mcp`. */
    path?: string;
    log?: (message: string) => void;
}
export interface RunningHttpServer {
    url: string;
    close(): Promise<void>;
}
export declare function runHttpServer(createServer: () => McpServer, { port, host, path, log, }?: HttpServerOptions): Promise<RunningHttpServer>;
