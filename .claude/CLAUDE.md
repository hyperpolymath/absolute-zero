# Project Instructions

## Package Manager Policy (RSR)

- **REQUIRED**: Deno for JavaScript/TypeScript
- **FORBIDDEN**: npm, npx, node_modules, package-lock.json
- **FORBIDDEN**: bun (unless Deno is technically impossible)

When asked to add npm packages, use Deno alternatives:
- `npm install X` → Add to import_map.json or use npm: specifier
- `npm run X` → `deno task X`

## Language Policy (RSR)

### ⚠️ CONVERSION IN PROGRESS: TS/JS → ReScript

- **REQUIRED**: ReScript for all NEW code
- **FORBIDDEN**: New TypeScript/JavaScript files
- **TODO**: Convert existing TS/JS to ReScript
- **ALLOWED**: Generated .res.js files

See TS_CONVERSION_NEEDED.md for migration status.
