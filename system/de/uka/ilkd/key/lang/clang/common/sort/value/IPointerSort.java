package de.uka.ilkd.key.lang.clang.common.sort.value;

import de.uka.ilkd.key.lang.clang.common.sort.IClangObjectSort;
import de.uka.ilkd.key.lang.clang.common.sort.IClangValueSort;

public interface IPointerSort extends IClangValueSort {

        /**
         * Returns pointer sort's target sort.
         * @return
         */
        IClangObjectSort getTargetSort();
}