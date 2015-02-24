// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.util;

/**
 * Utility class to select elements.
 * @author Martin Hentschel
 */
public interface IFilter<T> {
    /**
     * Checks if the given element should be selected.
     * @param element The element to test.
     * @return {@code true} handle element, {@code false} ignore element.
     */
    public boolean select(T element);
}