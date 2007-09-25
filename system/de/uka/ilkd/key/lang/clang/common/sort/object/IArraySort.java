package de.uka.ilkd.key.lang.clang.common.sort.object;

import java.math.BigInteger;

import de.uka.ilkd.key.lang.clang.common.sort.IClangObjectSort;

public interface IArraySort extends IInstantiableObjectSort {

        /**
         * Returns array sort's element sort.
         * @return
         */
        IInstantiableObjectSort getElemSort();

        /**
         * Returns array sort's size.
         * @return
         */
        BigInteger getSize();
}