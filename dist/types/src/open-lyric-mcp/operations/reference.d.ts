import '../headless.ts';
/**
 * What the notation is, as data: the bundled example songs, the section
 * (fence) types, the Config fields, and the notation reference itself —
 * `.claude/open-lyric/schema.md`, the same document the `open-lyric` package
 * ships, bundled whole so the server never disagrees with it.
 */
export interface ExampleSummary {
    id: string;
    fileName: string;
    title: string;
    description: string;
}
export declare function listExamples(): ExampleSummary[];
export declare function getExample(id: string): ExampleSummary & {
    text: string;
};
export declare function getNotationDocument(): string;
export interface NotationSection {
    /** `1`, `3`, `8` … (the `## N.` heading number). */
    id: string;
    title: string;
    text: string;
}
/** The reference split at its `## N. Title` headings. */
export declare function listNotationSections(): NotationSection[];
export declare function getNotationSection(idOrTitle: string): NotationSection;
/** §8.1 — every fence, pattern, enum and diagnostic, as data. */
export declare function getNotationGrammar(): Record<string, unknown>;
/** §8.2 — the JSON Schema (draft 2020-12) of a song object. */
export declare function getSongJsonSchema(): Record<string, unknown>;
export interface FenceTypeInfo {
    header: string;
    kind: string;
    description: string;
    numbered: boolean;
    required: boolean;
    /** Whether one part name may be declared more than once. */
    allowsDuplicates: boolean;
    /** The `Structure` code, or null (Config). */
    structureCode: string | null;
    /** `lyric`, `progression`, `mixed`, `freeText` or `config` (reference §2). */
    bodyRule: string;
    bodyRuleDescription: string;
    /** The fence opening line, e.g. ```` ```ol:Verse 1 ````. */
    example: string;
}
export declare function listFenceTypes(): FenceTypeInfo[];
export interface ConfigFieldInfo {
    name: string;
    required: boolean;
    multiline: boolean;
    aliases: string[];
    /** The closed value set, for enum fields. */
    values?: string[];
    /** The value pattern, for pattern fields (a JS regex source). */
    pattern?: string;
    note: string;
}
export declare function listConfigFields(): ConfigFieldInfo[];
export declare function listKeys(): string[];
export declare function listStructureCodes(): {
    code: string;
    header: string;
    numbered: boolean;
}[];
