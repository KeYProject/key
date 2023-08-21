/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Wraps a list of expressions.
 */
public final class SLParameters {

    private final ImmutableList<SLExpression> parameters;

    public SLParameters(ImmutableList<SLExpression> parameters) {
        this.parameters = parameters;
    }


    public ImmutableList<SLExpression> getParameters() {
        return parameters;
    }


    public boolean isListOfTerm() {
        for (SLExpression expr : parameters) {
            if (!expr.isTerm()) {
                return false;
            }
        }
        return true;
    }

    /**
     * returns the type signature of the parameter list
     *
     * @param services the Services
     * @return the list of types that compose the type signature
     */
    public ImmutableList<KeYJavaType> getSignature(Services services) {
        ImmutableList<KeYJavaType> result = ImmutableSLList.nil();
        for (SLExpression expr : parameters) {
            KeYJavaType type = expr.getType();
            if (type == null) {
                final Term term = expr.getTerm();
                if (term != null) {
                    if (term.sort() == Sort.FORMULA) {
                        type = services.getTypeConverter().getBooleanType();
                    }
                }
            }
            result = result.append(type);
        }
        return result;
    }

    public String toString() {
        return parameters == null ? "" : parameters.toString();
    }


}
