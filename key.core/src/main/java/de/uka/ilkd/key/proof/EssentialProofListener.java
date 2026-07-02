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
 * <p>
 * <b>Failure semantics.</b> The marker also decides what happens when a listener throws while
 * handling an event (see {@code Proof#notifyListeners}): a non-essential observer is logged and
 * unregistered and the proof search continues -- its brokenness cannot corrupt the proof. A
 * failing <em>essential</em> listener, in contrast, means the proving machinery itself is broken
 * and the step that fired the event may already have left the proof or a goal inconsistent:
 * the proof is then marked {@linkplain Proof#isErroneous() erroneous}, which cooperatively stops
 * the running search and refuses to start a new one, while the proof object stays intact so the
 * user can still save it for a later reload attempt.
 *
 * @author Claude (KeY multithreading effort)
 * @see Proof#suspendNonEssentialListeners()
 * @see Proof#isErroneous()
 */
public interface EssentialProofListener {
}
