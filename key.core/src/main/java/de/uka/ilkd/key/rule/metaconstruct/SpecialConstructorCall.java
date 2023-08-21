/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.SpecialConstructorReference;
import de.uka.ilkd.key.java.reference.ThisConstructorReference;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * The constructor call meta construct is used to handle a allocation expression like
 * <code>new Class(...)</code>. Thereby it replaces the allocation expression by a method reference
 * to an implict method called <code>&lt;init&gt;</code> that is mainly the constructor but in its
 * normalform.
 */
public class SpecialConstructorCall extends ProgramTransformer {

    /**
     * The normal form identifier {@link ProgramElementName}.
     */
    private static final ProgramElementName NORMALFORM_IDENTIFIER =
        new ProgramElementName(de.uka.ilkd.key.java.recoderext.//
                ConstructorNormalformBuilder.CONSTRUCTOR_NORMALFORM_IDENTIFIER);

    /**
     * @param consRef The constructor reference.
     */
    public SpecialConstructorCall(ProgramElement consRef) {
        super(new Name("special-constructor-call"), consRef);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {

        SpecialConstructorReference constructorReference = (SpecialConstructorReference) pe;

        ReferencePrefix prefix;
        if (constructorReference instanceof ThisConstructorReference) {
            prefix = KeYJavaASTFactory.thisReference();
        } else {
            prefix = KeYJavaASTFactory.superReference();
        }

        return new ProgramElement[] { KeYJavaASTFactory.methodCall(prefix, NORMALFORM_IDENTIFIER,
            constructorReference.getArguments()) };
    }

}
