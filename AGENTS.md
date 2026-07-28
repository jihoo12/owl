<!-- code-review-graph MCP tools -->
## MCP Tools: code-review-graph

**IMPORTANT: This project has a knowledge graph. ALWAYS use the
code-review-graph MCP tools BEFORE using Grep/Glob/Read to explore
the codebase.** The graph is faster, cheaper (fewer tokens), and gives
you structural context (callers, dependents, test coverage) that file
scanning cannot.

### When to use graph tools FIRST

- **Exploring code**: `semantic_search_nodes_tool` or `query_graph_tool` instead of Grep
- **Understanding impact**: `get_impact_radius_tool` instead of manually tracing imports
- **Code review**: `detect_changes_tool` + `get_review_context_tool` instead of reading entire files
- **Finding relationships**: `query_graph_tool` with callers_of/callees_of/imports_of/tests_for
- **Architecture questions**: `get_architecture_overview_tool` + `list_communities_tool`

Fall back to Grep/Glob/Read **only** when the graph doesn't cover what you need.

### Key Tools

| Tool | Use when |
| ------ | ---------- |
| `detect_changes_tool` | Reviewing code changes — gives risk-scored analysis |
| `get_review_context_tool` | Need source snippets for review — token-efficient |
| `get_impact_radius_tool` | Understanding blast radius of a change |
| `get_affected_flows_tool` | Finding which execution paths are impacted |
| `query_graph_tool` | Tracing callers, callees, imports, tests, dependencies |
| `semantic_search_nodes_tool` | Finding functions/classes by name or keyword |
| `get_architecture_overview_tool` | Understanding high-level codebase structure |
| `refactor_tool` | Planning renames, finding dead code |

### Workflow

1. The graph auto-updates on file changes (via hooks).
2. Use `detect_changes_tool` for code review.
3. Use `get_affected_flows_tool` to understand impact.
4. Use `query_graph_tool` pattern="tests_for" to check coverage.


---

<!-- code-review-graph MCP tools -->
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
