/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

import java.util.List;

import recoder.ProgramFactory;
import recoder.abstraction.ClassType;
import recoder.abstraction.Member;
import recoder.java.Declaration;
import recoder.java.declaration.DeclarationSpecifier;
import recoder.java.declaration.MemberDeclaration;
import recoder.java.declaration.Modifier;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.modifier.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.ChangeHistory;
import recoder.service.SourceInfo;
import recoder.util.Debug;

/**
 * this class implements basic functions for modifier handling.
 *
 * @author Andreas Ludwig
 * @author Rainer Neumann
 */
public class ModifierKit implements recoder.bytecode.AccessFlags {

    /**
     * The virtual "package" modifier code.
     */
    public final static int PACKAGE = INTERFACE;

    private ModifierKit() {
        super();
    }

    public static Modifier createModifier(ProgramFactory f, int code) {
        Debug.assertNonnull(f);
        switch (code) {
        case PACKAGE:
            return null;
        case PUBLIC:
            return f.createPublic();
        case PROTECTED:
            return f.createProtected();
        case PRIVATE:
            return f.createPrivate();
        case STATIC:
            return f.createStatic();
        case FINAL:
            return f.createFinal();
        case ABSTRACT:
            return f.createAbstract();
        case SYNCHRONIZED:
            return f.createSynchronized();
        case TRANSIENT:
            return f.createTransient();
        case STRICT:
            return f.createStrictFp();
        case VOLATILE:
            return f.createVolatile();
        case NATIVE:
            return f.createNative();
        default:
            throw new IllegalArgumentException("Unsupported modifier code " + code);
        }
    }

    public static int getCode(Modifier m) {
        if (m == null) {
            return PACKAGE;
        }
        if (m instanceof VisibilityModifier) {
            if (m instanceof Public) {
                return PUBLIC;
            } else if (m instanceof Protected) {
                return PROTECTED;
            } else if (m instanceof Private) {
                return PRIVATE;
            }
        } else if (m instanceof Static) {
            return STATIC;
        } else if (m instanceof Final) {
            return FINAL;
        } else if (m instanceof Abstract) {
            return ABSTRACT;
        } else if (m instanceof Synchronized) {
            return SYNCHRONIZED;
        } else if (m instanceof Transient) {
            return TRANSIENT;
        } else if (m instanceof StrictFp) {
            return STRICT;
        } else if (m instanceof Volatile) {
            return VOLATILE;
        } else if (m instanceof Native) {
            return NATIVE;
        }
        throw new IllegalArgumentException("Unknown Modifier " + m.getClass().getName());
    }

    public static VisibilityModifier getVisibilityModifier(Declaration decl) {
        Debug.assertNonnull(decl);
        List<DeclarationSpecifier> mods = decl.getDeclarationSpecifiers();
        if (mods == null) {
            return null;
        }
        for (DeclarationSpecifier res : mods) {
            if (res instanceof VisibilityModifier) {
                return (VisibilityModifier) res;
            }
        }
        return null;
    }

    private static boolean containsModifier(Declaration decl, Class mod) {
        Debug.assertNonnull(decl, mod);
        List<DeclarationSpecifier> mods = decl.getDeclarationSpecifiers();
        if (mods == null) {
            return false;
        }
        for (DeclarationSpecifier res : mods) {
            if (mod.isInstance(res)) {
                return true;
            }
        }
        return false;
    }

    // does not check vadility, but replaces an existing visibility modifier
    // if there is one. Understands the PACKAGE_VISIBILITY pseudo modifier.
    // obeys the standard JavaDOC modifier order convention:
    // VisibilityModifier as first, then abstract or (static - final)
    // all others go to the last position
    /**
     * @deprecated replaced by recoder.kit.transformation.Modify
     */
    @Deprecated
    private static DeclarationSpecifier modify(ChangeHistory ch, int code, Declaration decl) {
        Debug.assertNonnull(decl);
        ASTList<DeclarationSpecifier> mods = decl.getDeclarationSpecifiers();
        ProgramFactory fact = decl.getFactory();
        DeclarationSpecifier m;
        int insertPos = 0;
        switch (code) {
        case PACKAGE:
            if (code == PACKAGE) {
                m = getVisibilityModifier(decl);
                if (m != null) {
                    MiscKit.remove(ch, m);
                }
                return null;
            }
        case PUBLIC:
            m = getVisibilityModifier(decl);
            if (m instanceof Public) {
                return null;
            }
            if (m != null) {
                MiscKit.remove(ch, m);
            }
            if (mods == null) {
                mods = new ASTArrayList<>();
                decl.setDeclarationSpecifiers(mods);
            }
            m = fact.createPublic();
            insertPos = 0;
            break;
        case PROTECTED:
            m = getVisibilityModifier(decl);
            if (m instanceof Protected) {
                return null;
            }
            if (m != null) {
                MiscKit.remove(ch, m);
            }
            if (mods == null) {
                mods = new ASTArrayList<>();
                decl.setDeclarationSpecifiers(mods);
            }
            m = fact.createProtected();
            insertPos = 0;
            break;
        case PRIVATE:
            m = getVisibilityModifier(decl);
            if (m instanceof Private) {
                return null;
            }
            if (m != null) {
                MiscKit.remove(ch, m);
            }
            if (mods == null) {
                mods = new ASTArrayList<>();
                decl.setDeclarationSpecifiers(mods);
            }
            m = fact.createPrivate();
            insertPos = 0;
            break;
        case STATIC:
            if (containsModifier(decl, Static.class)) {
                return null;
            }
            m = getVisibilityModifier(decl);
            insertPos = (m == null) ? 0 : 1;
            m = fact.createStatic();
            break;
        case FINAL:
            if (containsModifier(decl, Final.class)) {
                return null;
            }
            m = getVisibilityModifier(decl);
            insertPos = (m == null) ? 0 : 1;
            if (containsModifier(decl, Static.class)) {
                insertPos += 1;
            }
            m = fact.createFinal();
            break;
        case ABSTRACT:
            if (containsModifier(decl, Abstract.class)) {
                return null;
            }
            m = getVisibilityModifier(decl);
            insertPos = (m == null) ? 0 : 1;
            m = fact.createAbstract();
            break;
        case SYNCHRONIZED:
            if (containsModifier(decl, Synchronized.class)) {
                return null;
            }
            insertPos = (mods == null) ? 0 : mods.size();
            m = fact.createSynchronized();
            break;
        case TRANSIENT:
            if (containsModifier(decl, Transient.class)) {
                return null;
            }
            insertPos = (mods == null) ? 0 : mods.size();
            m = fact.createTransient();
            break;
        case STRICT:
            if (containsModifier(decl, StrictFp.class)) {
                return null;
            }
            insertPos = (mods == null) ? 0 : mods.size();
            m = fact.createStrictFp();
            break;
        case VOLATILE:
            if (containsModifier(decl, Volatile.class)) {
                return null;
            }
            insertPos = (mods == null) ? 0 : mods.size();
            m = fact.createVolatile();
            break;
        case NATIVE:
            if (containsModifier(decl, Native.class)) {
                return null;
            }
            insertPos = (mods == null) ? 0 : mods.size();
            m = fact.createNative();
            break;
        default:
            throw new IllegalArgumentException("Unsupported modifier code " + code);
        }
        mods.add(insertPos, m);
        m.setParent(decl); // make parent role valid
        if (ch != null) {
            ch.attached(m);
        }
        return m;
    }

    // mdecl must be a valid recoder.abstraction.Member (not a class
    // initializer)
    // returns true if nothing was to be done
    // does not check if private would be sufficient dealing with multiple
    // inner types; this case rarely occurs and will be handled by assigning
    // package visibility -- which also is what a byte code compiler would
    // generate anyway.

    /**
     * @return true if made visible
     * @deprecated will be replaced; does not make visible redefined members
     */
    @Deprecated
    public static boolean makeVisible(ChangeHistory ch, SourceInfo si, MemberDeclaration mdecl,
            ClassType ct) {
        Debug.assertNonnull(si, mdecl, ct);
        Debug.assertBoolean(mdecl instanceof Member);
        if (si.isVisibleFor((Member) mdecl, ct)) {
            return true;
        }
        int minimumNeeded;
        TypeDeclaration mt = mdecl.getMemberParent();
        if (mt == ct) {
            minimumNeeded = PRIVATE;
        } else if (mt.getPackage() == ct.getPackage()) {
            minimumNeeded = PACKAGE;
        } else if (si.isSubtype(mt, ct)) {
            minimumNeeded = PROTECTED;
        } else {
            minimumNeeded = PUBLIC;
        }
        modify(ch, minimumNeeded, mdecl);
        return false;
    }

}
