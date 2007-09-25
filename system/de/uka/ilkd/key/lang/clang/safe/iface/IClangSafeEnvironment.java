package de.uka.ilkd.key.lang.clang.safe.iface;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;

/**
 * Safe CDL specific language environment.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface IClangSafeEnvironment extends IClangEnvironment {
        IClangSafePlatform getSafePlatform();
}
