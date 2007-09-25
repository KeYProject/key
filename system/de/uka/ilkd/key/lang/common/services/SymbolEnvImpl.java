package de.uka.ilkd.key.lang.common.services;

import java.math.BigInteger;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * A standard implementation of symbol environment.
 * 
 * @author oleg.myrk@gmail.com
 */
public class SymbolEnvImpl implements ISymbolEnv {
        private Namespace sortNS;

        private Namespace symbolNS;

        public SymbolEnvImpl(Namespace sortNS, Namespace symbolNS) {
                this.sortNS = sortNS;
                this.symbolNS = symbolNS;
        }

        /**
         * @inheritDocs
         */
        public Namespace getSortNS() {
                return sortNS;
        }

        /**
         * @inheritDocs
         */
        public Namespace getSymbolNS() {
                return symbolNS;
        }

        /**
         * @inheritDocs
         */
        public Sort getBooleanSort() {
                return (Sort) sortNS.lookup(new Name("boolean"));
        }

        /**
         * @inheritDocs
         */
        public Sort getIntSort() {
                return (Sort) sortNS.lookup(new Name("int"));
        }

        /**
         * @inheritDocs
         */
        public Sort getNullSort() {
                return Sort.NULL;
        }

        /**
         * @inheritDocs
         */
        public Function getNullConstant() {
                return Op.NULL;
        }

        /**
         * @inheritDocs
         */
        public Term encodeInteger(BigInteger value) {
                Function numbers = (Function) symbolNS.lookup(new Name("Z"));
                Function minus = (Function) symbolNS.lookup(new Name("neglit"));
                Function base = (Function) symbolNS.lookup(new Name("#"));

                Term result = TermFactory.DEFAULT.createFunctionTerm(base);

                String literalString = value.toString();

                boolean minusFlag = false;
                if (literalString.charAt(0) == '-') {
                        minusFlag = true;
                        literalString = literalString.substring(1);
                }

                char[] int_ch = literalString.toCharArray();
                for (int i = 0; i < int_ch.length; i++) {
                        result = TermFactory.DEFAULT.createFunctionTerm(
                                        (Function) symbolNS.lookup(new Name(""
                                                        + (int_ch[i] - '0'))),
                                        result);
                }
                if (minusFlag) {
                        result = TermFactory.DEFAULT.createFunctionTerm(minus,
                                        result);
                }
                result = TermFactory.DEFAULT
                                .createFunctionTerm(numbers, result);

                return result;
        }

        /**
         * @inheritDocs
         */
        public BigInteger parseInteger(Term term) {
                Function numbers = (Function) symbolNS.lookup(new Name("Z"));
                Function minus = (Function) symbolNS.lookup(new Name("neglit"));
                Function base = (Function) symbolNS.lookup(new Name("#"));

                Operator top = term.op();

                // check whether term is really an integer literal
                if (!top.name().equals(numbers.name()))
                        throw new NumberFormatException(
                                        "The term is not an integer literal");

                term = term.sub(0);
                top = term.op();

                boolean neg = false;
                while (top.name().equals(minus.name())) {
                        neg = !neg;
                        term = term.sub(0);
                        top = term.op();
                }

                StringBuffer result = new StringBuffer();

                while (!top.name().equals(base.name())) {
                        result.append(top.name());
                        term = term.sub(0);
                        top = term.op();
                }

                if (neg)
                        result.append("-");

                result.reverse();

                return new BigInteger(result.toString());
        }

        /**
         * @inheritDocs
         */
        public Function getLessFunction() {
                return (Function) symbolNS.lookup(new Name("lt"));
        }

        /**
         * @inheritDocs
         */
        public Function getLessEqFunction() {
                return (Function) symbolNS.lookup(new Name("lteq"));
        }

        /**
         * @inheritDocs
         */
        public Function getGreaterFunction() {
                return (Function) symbolNS.lookup(new Name("gt"));
        }

        /**
         * @inheritDocs
         */
        public Function getGreaterEqFunction() {
                return (Function) symbolNS.lookup(new Name("gteq"));
        }
}
