/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang;


import java.util.function.UnaryOperator;

import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.util.collection.ImmutableList;

/**
 * A contract about an operation (i.e., a method or a constructor), consisting of a precondition, a
 * postcondition, a modifiable clause, a measured-by clause, and a modality.
 */
public interface FunctionalOperationContract extends OperationContract {
    @Override
    FunctionalOperationContract map(UnaryOperator<Term> op, Services services);

    /**
     * Returns the modality of the contract.
     */
    Modality.RustyModalityKind getModalityKind();

    Term getEnsures();

    /**
     * Returns the postcondition of the contract.
     *
     * @param selfVar the self variable.
     * @param paramVars the list of parameter variables.
     * @param resultVar the result variable.
     * @param services the services object.
     * @return the post condition.
     */
    Term getPost(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            Services services);


    String getBaseName();

    Term getPre();

    Term getPost();

    Term getModifiable();

    @Override
    Term getMby();

    Term getSelf();

    ImmutableList<Term> getParams();

    Term getResult();
}
