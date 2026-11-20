# Research data

| Path | Contents |
| --- | --- |
| [certificates/](certificates/) | Exact witnesses and structural input tables retained with their checks |
| [figures/](figures/) | Retained research illustrations, separate from generated plot batches |
| [layout.json](layout.json) | Original-to-current file map used by `code/run.py` |

The layout map records original paths and provenance, current file locations,
runnable entrypoints, and ordered source prerequisites. Multiple historical
paths can refer to one retained file. Provenance hashes describe original
content, not later prose edits.

Keep expensive-to-discover inputs here when a checker needs them. Put generated
reports, numerical search output, and temporary solver files in `build/`.
Historical mixed build records are preserved in the
[archive](../archive/README.md).

See [exact input conventions](../docs/certificates.md) and the
[execution guide](../docs/reproduction.md).
