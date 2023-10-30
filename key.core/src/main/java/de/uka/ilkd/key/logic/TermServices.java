/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.Modality;

/**
 * This interface defines the basic functionalities of services required to construct {@link Term}s.
 *
 * @author Richard Bubel
 */
public interface TermServices {

    /**
     * returns the namespaces for functions, predicates etc.
     *
     * @return the proof specific namespaces
     */
    NamespaceSet getNamespaces();

    /**
     * Retrieves the modality of the given kind and program.
     *
     * @param kind the kind of the modality such as diamond or box
     * @param jb the program of this modality
     * @return the modality of the given kind and program.
     */
    Modality getModality(Modality.JavaModalityKind kind, JavaBlock jb);

    /**
     * Returns the {@link TermBuilder} used to create {@link Term}s.
     *
     * @return The {@link TermBuilder} used to create {@link Term}s.
     */
    TermBuilder getTermBuilder();

    /**
     *
     * Returns either the cache backed or raw {@link TermBuilder} used to create {@link Term}s.
     * Usually the cache backed version is the intended one. The non-cached version is for use cases
     * where a lot of intermediate terms are created of which most exist only for a very short time.
     * To avoid polluting the cache it is then recommended to use the non-cache version
     *
     * @return The {@link TermBuilder} used to create {@link Term}s.
     */
    TermBuilder getTermBuilder(boolean withCache);

    /**
     * Returns the {@link TermBuilder} used to create {@link Term}s.
     *
     * @return The {@link TermBuilder} used to create {@link Term}s.
     */
    TermFactory getTermFactory();

}
