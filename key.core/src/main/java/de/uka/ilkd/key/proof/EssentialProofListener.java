/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

/**
 * Marker for proof listeners that are part of the proving machinery itself and must keep receiving
 * events even while non-essential observers are suspended.
 *
 * <p>
 * Background (multithreading effort, branch {@code bubel/mt-goals}): during automatic proof search
 * &mdash; especially once goals are processed on worker threads &mdash; we want to detach
 * everything that merely <em>observes</em> the proof (caching, slicing, origin labels, GUI tree
 * models, &hellip;) so that nothing unrelated to proving runs on a worker thread or mutates shared
 * state concurrently. {@link Proof#suspendNonEssentialListeners()} removes exactly those listeners
 * that are <strong>not</strong> tagged with this marker, and re-attaches them when the run
 * finishes.
 *
 * <p>
 * Apply this marker only to listeners that maintain state the prover itself relies on (e.g. proof
 * correctness / contract-dependency bookkeeping). Pure observers must <em>not</em> implement it.
 *
 * @author Claude (KeY multithreading effort)
 * @see Proof#suspendNonEssentialListeners()
 */
public interface EssentialProofListener {
}
