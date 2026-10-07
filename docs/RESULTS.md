# Putnam results and evaluation scope

**672 distinct Putnam problems with saved solutions**, as of October 7, 2026.
The cumulative archive covers every problem identifier in the evaluated
672-problem PutnamBench corpus.

The project archive and PutnamBench's public listing describe different records:

| Record | Problems | Date | Evidence |
| --- | ---: | --- | --- |
| Cumulative saved solutions | **672 distinct problems** | October 7, 2026 | Distinct Putnam problem identifiers in the project’s local solved archive |
| PutnamBench listing | **65 problems** | Public data checked October 7, 2026 | [Leaderboard](https://trishullab.github.io/PutnamBench/leaderboard.html) and [results metadata](https://trishullab.github.io/PutnamBench/results.json) |

The archive combines models, configurations, and budgets; it is not a controlled
benchmark solve rate. The earlier 65-problem listing is included in the total.

Each `putnam_YEAR_aN` / `putnam_YEAR_bN` identifier counts once across current and
archived solutions. Duplicate proofs and repeat solves do not increase the count.
The proof files are not bundled with this repository.

## Corpus coverage

| Problem years | Distinct problems with saved solutions |
| --- | ---: |
| 1962–1969 | 90 |
| 1970–1979 | 101 |
| 1980–1989 | 98 |
| 1990–1999 | 103 |
| 2000–2009 | 103 |
| 2010–2019 | 111 |
| 2020–2025 | 66 |
| **Total** | **672** |

These counts follow the benchmark corpus; they do not include every historical
Putnam problem from those years.

## Verification and evaluation scope

Saved solutions retain individual verification and axiom records. The cumulative
count does not imply that every historical artifact meets the current export
policy. Use a verified export for the intended theorem and Lean project when
reporting a formal result.

## The earlier 65-problem submission

<a id="the-65-listed-problem-identifiers"></a>

The proof bundle was submitted privately to the PutnamBench verification team
on August 31, 2026. The project publishes the identifiers below; the benchmark
proof files and answers are not included in this repository.

| Period | Problems |
| --- | --- |
| 1960s | `1962 A6`, `1963 B1`, `1964 B1`, `1964 B2`, `1965 A4`, `1965 A6`, `1966 A1`, `1968 A1`, `1968 B2`, `1969 A1` |
| 1970s | `1970 B3`, `1971 A1`, `1971 B1`, `1972 A1`, `1972 A2`, `1973 B2`, `1975 B1`, `1977 A2`, `1977 A3`, `1977 A5`, `1978 A1`, `1978 A4`, `1979 B6` |
| 1980s | `1986 A1`, `1986 B1`, `1986 B6`, `1987 A1`, `1987 A2`, `1988 B1`, `1988 B2` |
| 1990s | `1990 A1`, `1990 A5`, `1990 A6`, `1991 A2`, `1992 A1`, `1992 A2`, `1993 A2`, `1995 A1`, `1996 A3`, `1997 A4`, `1998 B1`, `1998 B2`, `1999 A1` |
| 2000s | `2000 A1`, `2000 B2`, `2001 A1`, `2003 B1`, `2004 A1`, `2004 B2`, `2005 A1`, `2005 B1`, `2006 A1`, `2007 B1`, `2008 A1`, `2009 A1` |
| 2010s | `2010 A2`, `2012 A2`, `2016 A1` |
| 2020s | `2021 A1`, `2021 A2`, `2024 A1`, `2024 B3`, `2025 A1`, `2025 B2`, `2025 B3` |

## Reading proof-search results

A recorded helper can be useful progress while the original theorem remains
unresolved. An internal root solve still needs its export check. Treat a
**verified export**, checked against the intended theorem and project, as the
proof certificate. For natural-language input, separately inspect whether the
formal statement represents the intended claim.

See [how to determine whether a run succeeded](USER_GUIDE.md#11-determine-whether-a-run-succeeded)
and [standalone exports](USER_GUIDE.md#12-standalone-exports-and-proof-graphs).
