// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.parser.ast;


import de.uka.ilkd.asmkey.util.ArrayUtil;
import de.uka.ilkd.key.parser.Location;


/** This class represents a proof.
 *
 * @author Stanislas Nanchen
 */
public class AstProof extends AstNode {

    public static final int PROP = 0;
    public static final int AXIOM = 1;
    public static final int TRUTH = 2;
    
    private int type;
    private AstTerm problem;
    private AstProofExpression[] logs;
    private AstProofExpression proof;
    private Identifier id;
    private String headerString;
    private boolean closed;

    private AstProof(int type, Location location, 
		     AstProofMeta meta, AstTerm problem,
		     AstProofExpression[] logs, AstProofExpression proof) {
	super(location);
	this.logs = logs;
	this.proof = proof;
	this.id = meta.id;
	this.headerString = meta.header;
	this.closed = meta.closed;
	this.type = type;
	this.problem = problem;
    }

    public int type() {
	return type;
    }
    
    public String headerString() {
	return headerString;
    }

    public Identifier getProofId() {
	return id;
    }
    
    public boolean closed() {
	return closed;
    }

    public AstProofExpression getProof() {
	return proof;
    }

    public AstProofExpression[] getLogs() {
	return logs;
    }


    /** for debug only */
    public String toString() {
        return "[AstProof:logs="+ ArrayUtil.toString(logs) + ",proof=" + proof + "]";
    }

    public static AstProof createPropAstProof(Location location,
					      AstProofMeta meta,
					      AstTerm problem,
					      AstProofExpression[] plogs,
					      AstProofExpression pexpr) {
	return new AstProof(PROP, location, meta, problem, plogs, pexpr);
    }

    public static AstProof createAxiomAstProof(Location location,
					       AstProofMeta meta,
					       AstTerm problem) {
	return new AstProof(AXIOM, location, meta, problem, null, null);
    }

    public static AstProof createTruthAstProof(Location location,
					       AstProofMeta meta,
					       AstTerm problem) {
	return new AstProof(TRUTH, location, meta, problem, null, null);
    }

}
