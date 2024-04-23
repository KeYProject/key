package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;

/**
 *
 * @author Alexander Weigl 
 * @version 1 (23.04.24)
 */
public record TranslatedDependencyContract(IObserverFunction first, Term second, Term third) {
}
