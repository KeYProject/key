package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.common.sort.IClangObjectSort;
import de.uka.ilkd.key.lang.clang.common.sort.IClangValueSort;
import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that creates either 
 * <code>isValidVal(#param)</code> or <code>isValidPtr(#param)</code>
 * depending on the type of <code>#param</code>.
 * 
 * @author oleg.myrk@gmail.com
 */
public class IsValidValueMetaOp extends SafeBaseMetaOp {

        public IsValidValueMetaOp() {
                super(new Name("#ClangIsValidValue"), 1);
        }
        
        /**
         * @inheritDocs
         */
        public Sort sort(Term[] term) {
                return Sort.FORMULA;
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangSafeEnvironment context) {
                Term term0 = term.sub(0);
                
                Sort valueSort = term0.sort();
                if (valueSort instanceof IClangValueSort)
                        return  TermFactory.DEFAULT.createFunctionTerm(context.getSafePlatform().getSafeValueMarkerSort().getIsValidValPredicate(), term0); 
                else if (valueSort instanceof IClangObjectSort)
                        return TermFactory.DEFAULT.createFunctionTerm(context.getSafePlatform().getSafeObjectMarkerSort().getIsValidPtrPredicate(), term0);
                else
                        throw new RuntimeException(
                                        "#ClangIsValidValue should be applied to a term of either value or object sort");
        }
}
