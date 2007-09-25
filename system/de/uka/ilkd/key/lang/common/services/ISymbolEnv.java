package de.uka.ilkd.key.lang.common.services;

import java.math.BigInteger;

import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Symbol environment provides access to the standard sorts and symbols
 * of the normal DL signature.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface ISymbolEnv {
        /**
         * Returns the current sort namespace.
         * @return
         */
        Namespace getSortNS();
        
        /**
         * Returns the current symbol namespace.
         * @return
         */
        Namespace getSymbolNS();
        
        /**
         * Returns the boolean sort.
         * 
         * @return
         */
        Sort getBooleanSort();

        /**
         * Returns the int sort.
         * 
         * @return
         */
        Sort getIntSort();

        /**
         * Returns the Null sort. Null sort extends all object sorts.
         * 
         * @return
         */
        Sort getNullSort();

        /**
         * Returns the null function. Represents the only element of Null sort.
         * 
         * @return
         */
        Function getNullConstant();

        /**
         * Encodes integer as a term.
         * 
         * @param integer
         * @return
         */
        Term encodeInteger(BigInteger integer);

        /**
         * Parses integer term.
         * 
         * @param term
         * @return parsed integer
         * @throws NumberFormatException
         *                 if the term does not reperesent integer constant.
         */
        BigInteger parseInteger(Term term) throws NumberFormatException;

        /**
         * Returns the integer Less function.
         * 
         * @return
         */
        Function getLessFunction();

        /**
         * Returns the integer LessEq function.
         * 
         * @return
         */
        Function getLessEqFunction();

        /**
         * Returns the integer Greater function.
         * 
         * @return
         */
        Function getGreaterFunction();

        /**
         * Returns the integer GreaterEq function.
         * 
         * @return
         */
        Function getGreaterEqFunction();
        
        // TODO: add the rest of the signature
}
