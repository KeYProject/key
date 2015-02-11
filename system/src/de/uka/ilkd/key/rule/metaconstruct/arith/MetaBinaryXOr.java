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

package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.logic.Name;


public final class MetaBinaryXOr extends MetaArithBitMaskOp {

	public MetaBinaryXOr() {
		super(new Name("#BinaryXOr"));
	}


	@Override
    protected BigInteger bitmaskOp(BigInteger left, BigInteger right) {
		return left.xor(right);
	}
}