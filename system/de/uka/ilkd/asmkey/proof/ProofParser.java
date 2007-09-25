// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.proof;


import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.StringTokenizer;

import de.uka.ilkd.asmkey.parser.ast.AstProofExpression;
import de.uka.ilkd.asmkey.parser.ast.AstProofExpressionType;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.util.Debug;


/** Class translates an AST proof expression into a {@link
 * ProofNode}. The ProofNode contains more structure, while AST proof
 * expression allow arbitrary S-lists.
 *
 * @author Hubert Schmid */

public final class ProofParser {

    private ProofParser() {}

    /** Translate a AST proof expression into a ProofNode. */
    public static ProofNode parse(AstProofExpression expr) {
        return parseBranch(expr);
    }

    private static ProofNode parseBranch(AstProofExpression expr) {
        Debug.assertTrue(expr.getType() == AstProofExpressionType.BRANCH);
        List rules = new ArrayList();
        List nodes = new ArrayList();
        for (Iterator i = expr.getChildren().iterator(); i.hasNext();) {
            AstProofExpression child = (AstProofExpression) i.next();
            if (child.getType() == AstProofExpressionType.RULE) {
                rules.add(parseTaclet(child));
	    } else if (child.getType() == AstProofExpressionType.BUILTIN) {
		rules.add(parseBuiltIn(child));
            } else if (child.getType() == AstProofExpressionType.BRANCH) {
                nodes.add(parseBranch(child));
            } else if (child.getType() == AstProofExpressionType.IDENT) {
                // nothing
            } else {
                throw new RuntimeException("not supported.");
            }
        }
        return new ProofNode((ProofRule[]) rules.toArray(new ProofRule[rules.size()]),
                             (ProofNode[]) nodes.toArray(new ProofNode[nodes.size()]));
    }

    private static ProofBuiltIn parseBuiltIn(AstProofExpression expr) {
	Debug.assertTrue(expr.getType() == AstProofExpressionType.BUILTIN);
	/* Collect all information and create a new ProofRule. */
	int formula = -1;
        PosInTerm pos = PosInTerm.TOP_LEVEL;
	boolean interactive = false;
	for (Iterator i = expr.getChildren().iterator(); i.hasNext();) {
            AstProofExpression child = (AstProofExpression) i.next();
            if (child.getType() == AstProofExpressionType.FORMULA) {
                formula = Integer.parseInt(child.getText());
            } else if (child.getType() == AstProofExpressionType.TERM) {
                pos = PosInTerm.parseReverseString(child.getText());
            } else if (child.getType() == AstProofExpressionType.INTERACTIVE) {
                interactive = true;
            } else {
                Debug.fail("not supported proof expression type: " + child.getType());
            }
        }
        if (formula == -1) {
            /* no formula expression found , we have a noFindTaclet*/
            Debug.fail("noFind built-in taclet not supported: " + expr.getText());
	    pos = null;
	    //SN: to think, we support no find builtin....
        }
        return new ProofBuiltIn(expr.getText(),
				formula,
				pos,
				interactive);
    }

    private static ProofTaclet parseTaclet(AstProofExpression expr) {
        Debug.assertTrue(expr.getType() == AstProofExpressionType.RULE);
        /* Collect all information and create a new ProofRule. */
        int formula = -1;
        PosInTerm pos = PosInTerm.TOP_LEVEL;
        List instantiations = new ArrayList();
        boolean interactive = false;
        List heuristics = null;
        List ifSeqFormulaList = new ArrayList();
        for (Iterator i = expr.getChildren().iterator(); i.hasNext();) {
            AstProofExpression child = (AstProofExpression) i.next();
            if (child.getType() == AstProofExpressionType.FORMULA) {
                formula = Integer.parseInt(child.getText());
            } else if (child.getType() == AstProofExpressionType.TERM) {
                pos = PosInTerm.parseReverseString(child.getText());
            } else if (child.getType() == AstProofExpressionType.INST) {
                String text = child.getText();
                int eq = text.indexOf('=');
                if (eq == -1) {
                    throw new RuntimeException("instantiation must contain '='.");
                }
                instantiations.add(new ProofInstantiation(text.substring(0, eq), text.substring(eq + 1)));
            } else if (child.getType() == AstProofExpressionType.INTERACTIVE) {
                interactive = true;
            } else if (child.getType() == AstProofExpressionType.HEURISTICS) {
                heuristics = new ArrayList();
                StringTokenizer st = new StringTokenizer(child.getText(), ",");
                while (st.hasMoreTokens()) {
                    heuristics.add(st.nextToken().trim());
                }
            } else if (child.getType() == AstProofExpressionType.IFSEQFORMULA) {
                ifSeqFormulaList.add(Integer.valueOf(child.getText()));
            } else {
                Debug.fail("not supported proof expression type: " + child.getType());
            }
        }
        if (formula == -1) {
            /* no formula expression found */
            //Debug.fail("not supported.");
	    pos = null;
        }
        return new ProofTaclet(expr.getText(),
                             formula,
                             pos,
                             (ProofInstantiation[]) instantiations.toArray(new ProofInstantiation[instantiations.size()]),
                             interactive,
                             heuristics == null ? null : (String[]) heuristics.toArray(new String[heuristics.size()]),
                             (Integer[]) ifSeqFormulaList.toArray(new Integer[ifSeqFormulaList.size()]));
    }

}
