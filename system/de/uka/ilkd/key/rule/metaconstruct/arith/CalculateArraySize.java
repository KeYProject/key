// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
/** this class implements the interface for
* MetaAdderators. MetaAdderators are used to do complex term
* transformation when applying a taclet. Often these transformation
* caanot be described with the taclet scheme (or trying to do so would
* result in a huge number of rules)
*/
public class CalculateArraySize extends AbstractMetaOperator {

    private static BigInteger eight=new BigInteger("8");
    private static BigInteger twelve=new BigInteger("12");
    private static BigInteger sixteen=new BigInteger("16");
    private static BigInteger zero=new BigInteger("0");
    
    public CalculateArraySize() {
        super(new Name("#calculateArraySize"), 2);
    }

    /** calculates the resulting term. */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        Term arg1 = term.sub(0);
        Term arg2 = term.sub(1);
        BigInteger longArg1=null;
        BigInteger longArg2=null;
        BigInteger product=null;
                
        longArg1 = new
            BigInteger(convertToDecimalString(arg1, services));
        longArg2 = new
            BigInteger(convertToDecimalString(arg2, services));
        if(longArg2.compareTo(zero)==-1){
            return services.getTypeConverter().convertToLogicElement(new IntLiteral("0"));
        }
        product = longArg1.multiply(longArg2).add(twelve);

        BigInteger result;
        
        if(product.compareTo(sixteen)==-1){
            result = sixteen;
        }else if(product.mod(eight).compareTo(zero)==0){
            result = product;
        }else{
            result = product.add(eight).subtract(product.mod(eight));
        }
        
        IntLiteral lit = new IntLiteral(result.toString());
        return services.getTypeConverter().convertToLogicElement(lit);

    }

}

