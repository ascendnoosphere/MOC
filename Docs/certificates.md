# Exact input data

The [boundary-chain verifier](../Code/verify_cone82.py) reads [cone82.json](../data/cone82.json) relative to its own location. The [C++ facet audit](../Code/audit_82_exact.cpp) enumerates the facets independently.

The [certificate collection](../data/certificates/) contains exact witnesses and structural input tables. The [historical source map](../data/layout.json) records original paths, curated destinations, original SHA-256 values, runnable entrypoints and prerequisite sources from the larger collection. Byte-identical legacy aliases may share one destination. Hashes describe the original content before editorial changes.
