// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.jmltest;

/**
 * @author mbender@uni-koblenz.de
 */

import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.Notation;
import de.uka.ilkd.key.pp.NotationInfo;

public class JMLNotationInfo extends NotationInfo {

    public JMLNotationInfo() {
        super();
    }

    protected void createDefaultOpNotation() {
        tbl.put(Op.TRUE, new Notation.Constant("true", 130));
        tbl.put(Op.FALSE, new Notation.Constant("false", 130));
        tbl.put(Op.NOT, new Notation.Prefix("!", 60, 60));

        tbl.put(Op.AND, new Notation.Infix("&&", 50, 50, 60));
        tbl.put(Op.OR, new Notation.Infix("||", 40, 40, 50));
        tbl.put(Op.IMP, new Notation.Infix("==>", 30, 40, 30));
        tbl.put(Op.EQV, new Notation.Infix("<==>", 20, 20, 30));

        tbl.put(Op.ALL, new Notation.Quantifier("\\forall", 60, 60));
        tbl.put(Op.EX, new Notation.Quantifier("\\exists", 60, 60));
        tbl.put(Op.DIA, new Notation.Modality("\\<", "\\>", 60, 60));
        tbl.put(Op.BOX, new Notation.Modality("\\[", "\\]", 60, 60));
        tbl.put(Op.TOUT, new Notation.Modality("\\[[", "\\]]", 60, 60));
        Modality modalities[] = { Op.DIATRC, Op.BOXTRC, Op.TOUTTRC, Op.DIATRA,
                Op.BOXTRA, Op.TOUTTRA, Op.DIASUSP, Op.BOXSUSP, Op.TOUTSUSP };
        for (Modality modality : modalities)
            tbl
                    .put(modality, new Notation.Modality("\\"
                            + modality.name().toString(), "\\endmodality",
                            60, 60));

        tbl.put(Op.IF_THEN_ELSE, new Notation.IfThenElse(130, "("));
        tbl.put(Op.IF_EX_THEN_ELSE, new Notation.IfThenElse(130, "\\ifEx"));      

        // createNumLitNotation(IntegerLDT.getStaticNumberSymbol());

        tbl.put(Op.SUBST, new Notation.Subst());

    }

    protected void createDefaultTermSymbolNotation() {
        tbl.put(Function.class, new Notation.Function());
        tbl.put(LogicVariable.class, new Notation.VariableNotation());
        // tbl.put(SchemaVariable.class, new Notation.Variable());
        tbl.put(Metavariable.class, new Notation.MetavariableNotation());
        tbl.put(ProgramVariable.class, new Notation.VariableNotation());
        tbl.put(ProgramMethod.class, new Notation.JMLProgramMethod(121));
        tbl.put(Equality.class, new Notation.Infix("==", 70, 80, 80));
        tbl.put(QuanUpdateOperator.class, new Notation.QuanUpdate());
        tbl.put(AnonymousUpdate.class, new Notation.AnonymousUpdate());
        tbl
                .put(ShadowAttributeOp.class, new Notation.ShadowAttribute(121,
                        121));
        tbl.put(AttributeOp.class, new Notation.Attribute(121, 121));
        tbl.put(ShadowArrayOp.class, new Notation.ArrayNot(new String[] { "[",
                "]", "" }, 130, new int[] { 121, 0, 0 }));
        tbl.put(ArrayOp.class, new Notation.ArrayNot(new String[] { "[", "]" },
                130, new int[] { 121, 0 }));
        tbl.put(CastFunctionSymbol.class, new Notation.CastFunction("(", ")",
                120, 140));
        tbl.put(NRFunctionWithExplicitDependencies.class,
                new Notation.NRFunctionWithDependenciesNotation());
        tbl.put(ModalOperatorSV.class, new Notation.ModalSVNotation(60, 60));
        tbl.put(SortedSchemaVariable.class,
                new Notation.SortedSchemaVariableNotation());
    }

}
