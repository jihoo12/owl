# MCP Tools: rust-analyzer-db

This project uses **rust-analyzer-db** for Rust code analysis via MCP tools.

## Quick Start

1. First, scan the project: `scan_project(path="/path/to/project")`
2. Verify scan: `get_stats()`
3. Use analysis tools as needed

## Available Tools

### Scanning & Stats
| Tool | Description |
|------|-------------|
| `scan_project` | Scan Rust project and populate database |
| `get_stats` | Project overview (files, items, call edges) |
| `list_files` | List all scanned files |

### Code Querying
| Tool | Description |
|------|-------------|
| `search_code` | Search code by name, kind, pattern |
| `list_items` | List code items (with rich filtering) |
| `get_item` | Get specific code item details |
| `get_item_children` | Get child items (methods in impl, etc.) |
| `get_item_source` | Get source code of a code item |
| `get_item_generics` | Get generic params of a code item |
| `get_item_lifetimes` | Get lifetime params of a code item |
| `list_use_decls` | List use declarations |
| `list_extern_crates` | List extern crate declarations |

### Analysis
| Tool | Description |
|------|-------------|
| `complexity_report` | Find complex code |
| `most_complex_items` | Most complex items in project |
| `get_item_complexity` | Get complexity details |
| `call_graph_info` | Call graph analysis |
| `api_surface` | Public API surface |
| `module_structure` | Module hierarchy |

### Finding
| Tool | Description |
|------|-------------|
| `find_item` | Find item by name (fuzzy) |
| `callers_of` | Find functions that call a given function |
| `callees_of` | Find functions called by a given function |
| `find_unused_imports` | Find use declarations not referenced |
| `implementors_of_trait` | Find types implementing a trait |

### Large/Complex
| Tool | Description |
|------|-------------|
| `get_largest_files` | Largest files by LOC |
| `get_most_complex` | Most complex items |
| `find_dead_code` | Find unreferenced functions/classes |
| `file_metrics` | File-level metrics |

## Typical Flow

1. `scan_project(path="/path/to/rust/project")` → populate DB
2. `get_stats()` → verify extraction
3. `search_code(query="fn", kind="function")` → browse functions
4. `complexity_report(threshold=5)` → find hotspots
5. `call_graph_info(name="main")` → understand call flow
6. `api_surface()` → review public API

## Tips

- Use `kind` filter: "function", "method", "struct", "impl", "trait", etc.
- Results are paginated — use `offset` and `limit`.
- `call_graph_info` shows callers and callees (use `depth` 1-5).
- `complexity_report` sorts by cyclomatic complexity.
