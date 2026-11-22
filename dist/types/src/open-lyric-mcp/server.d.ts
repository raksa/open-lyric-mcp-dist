import './headless.ts';
import { McpServer } from '@modelcontextprotocol/sdk/server/mcp.js';
export interface OpenLyricMcpServerOptions {
    /**
     * Folders file tools may use, besides the roots the client announces. With
     * neither, the working directory.
     */
    roots?: string[];
    /** Never write a file: edits on a path return the text instead. */
    readOnly?: boolean;
    /** Base for relative roots, and the fallback root. Default `process.cwd()`. */
    cwd?: string;
    /** Replace the client roots lookup (tests, custom hosts). */
    listClientRoots?: () => Promise<string[] | null>;
}
export declare const OPEN_LYRIC_MCP_INSTRUCTIONS = "Open Lyric songs are Markdown documents with ```ol:<Section> fences: one ol:Config fence (Title and Structure required; Key, Tempo, Time, Locales \u2026) and one fence per section (Verse 1, Chorus, Bridge, Intro \u2026). Chords are [G] annotations placed just before the syllable they land on; Intro/Outro/Instrumental lines may be bar progressions (| G | D/F# |). Structure is the compact performance order, e.g. IV1CV2CBCx2O.\n\n- Before writing notation by hand, read open-lyric://docs/notation (or get_notation_reference).\n- Prefer the structural tools (create_song, add_section, rename_section, set_config_field, transpose_song \u2026): they keep Structure in step and return the validation.\n- After any change, make sure validate_song reports no errors; diagnostics carry 1-based lines and columns, and apply_fixes applies every one that carries a fix.\n- Song files (*.ol.md) are read and written only inside the allowed roots. Tools given a path edit that file in place \u2014 pass dryRun to preview.";
/**
 * An MCP server exposing the Open Lyric notation: validation, analysis, music
 * theory, structural editing, rendering and export, song files, reference
 * resources and prompts. Connect it to a transport (`runStdioServer`,
 * `runHttpServer`, or the SDK's own).
 */
export declare function createOpenLyricMcpServer(options?: OpenLyricMcpServerOptions): McpServer;
