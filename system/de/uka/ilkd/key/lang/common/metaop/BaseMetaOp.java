package de.uka.ilkd.key.lang.common.metaop;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.lang.common.services.ILangServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.MetaOperator;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Base implementation of meta operator.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseMetaOp extends Op implements MetaOperator {
        public static final Sort METASORT = new PrimitiveSort(new Name("Meta"));

        private int arity;

        public BaseMetaOp(Name name, int arity) {
                super(name);
                this.arity = arity;
        }

        /**
         * Calculates the result of applying the meta operation.
         * 
         * @param term
         * @param svInst
         * @param services
         * @param sortNS
         * @param symbolNS
         * @return
         */
        public abstract Term calculate(Term term, 
                        ILangServices services, Namespace sortNS,
                        Namespace symbolNS);

        /**
         * @inheritDocs
         */
        public Sort sort(Term[] term) {
                return METASORT;
        }

        /**
         * @inheritDocs
         */
        public int arity() {
                return arity;
        }

        /**
         * @inheritDocs
         */
        public boolean validTopLevel(Term term) {
                return term.arity() == arity();
        }

        /**
         * @deprecated
         */
        public final Term calculate(Term term, SVInstantiations svInst,
                        Services services) {
                return calculate(term, services.getLangServices(),
                                services.getNamespaces().sorts(), services
                                                .getNamespaces().functions());
        }
        /**
         * @deprecated
         */
        public MetaOperator getParamMetaOperator(String param) {
            return null;
        }        
}
