package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.metaop.BaseClangMetaOp;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that creates atomic update <code>{#param1 := #param2}#param3</code>.
 * 
 * @author oleg.myrk@gmail.com
 */
public class AtomicUpdateMetaOp extends BaseClangMetaOp {

        public AtomicUpdateMetaOp() {
                super(new Name("#ClangAtomicUpdate"), 3);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangEnvironment context) {
                Term term0 = term.sub(0);
                Term term1 = term.sub(1);
                Term term2 = term.sub(2);
                return TermFactory.DEFAULT.createUpdateTerm(term0, term1, term2);
        }
}
