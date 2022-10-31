// This file is part of the RECODER library and protected by the LGPL

package recoder.kit;

/**
 * Problem report indicating that the planned transformation breaks a contract even though there is
 * no typing conflict. Usually this may happen in the context of polymorph methods. This class of
 * problems is usually a conservative estimation only. Subclasses of this class may provide detailed
 * information about the reasons.
 */
public abstract class BrokenContract extends Problem {
    // nothing here
}

