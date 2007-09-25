// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.parser.ast;

/**
 * This class groups some meta information
 * about a proof.
 */
public class AstProofMeta {
    public final Identifier id;
    public final String header;
    public final boolean closed;

    public AstProofMeta(Identifier id, String header, boolean closed) {
	this.id = id;
	this.header = header;
	this.closed = closed;
    }
}
