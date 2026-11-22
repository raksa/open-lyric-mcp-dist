/** Small text helpers the operations share. */
export declare function normalizeNewlines(value: unknown): string;
export declare function splitLines(value: unknown): string[];
/** Count the 1-based line numbers whose text differs between two documents. */
export declare function countChangedLines(before: string, after: string): number;
export declare class SongOperationError extends Error {
}
