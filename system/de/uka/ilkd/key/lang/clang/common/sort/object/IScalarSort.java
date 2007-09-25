package de.uka.ilkd.key.lang.clang.common.sort.object;

import de.uka.ilkd.key.logic.sort.Sort;

public interface IScalarSort extends IInstantiableObjectSort {

        /**
         * Returns scalar sort's value sort.
         * @return
         */
        Sort getValueSort();
}