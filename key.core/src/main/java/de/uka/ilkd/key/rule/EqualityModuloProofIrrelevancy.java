/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.Objects;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.SuperArrayDeclaration;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.EqualsModProofIrrelevancyUtil;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import static de.uka.ilkd.key.logic.equality.ProofIrrelevancyProperty.PROOF_IRRELEVANCY_PROPERTY;

/**
 * Implements {@link de.uka.ilkd.key.logic.equality.EqualsModProperty} comparisons for
 * non term classes. This class can be used to make comparisons between different proofs.
 * This class is used by the Copying and Slicing proof replayer as they need to relate
 * different proofs and have therefore to rely on sort and type names instead of object
 * identity. Further more than just terms and programs must be compared.
 */
public class EqualityModuloProofIrrelevancy {
    // Operator
    /**
     * test for equality modulo proof irrelevancy for the given arguments
     *
     * @param _this the first Operator
     * @param that the second Operator
     * @return true if both arguments are equal modulo proof irrelevancy
     */
    public static boolean equalsModProofIrrelevancy(Operator _this, Operator that) {
        if (_this == that) {
            return true;
        } else if (that == null || _this == null) {
            return false;
        } else if (_this.getClass() != that.getClass()) {
            return false;
        }

        if (_this instanceof LogicVariable _thisLV) {
            return equalsModProofIrrelevancy(_thisLV, (LogicVariable) that);
        } else if (_this instanceof LocationVariable _thisLoc) {
            return equalsModProofIrrelevancy(_thisLoc, (LocationVariable) that);
        } else if (_this instanceof JModality _thisMod) {
            return _thisMod.kind().equals(((JModality) that).kind()) &&
                    equalsModProofIrrelevancy(_thisMod.programBlock(),
                        ((JModality) that).programBlock());
        }

        // assume name and arity uniquely identifies operator
        return _this.arity() == that.arity() && _this.name().equals(that.name());
    }

    /**
     * computes the hash code modulo proof irrelevancy for the given argument
     *
     * @param op the Operator for which to compute the hash
     * @return the hash code modulo proof irrelevancy for the given argument
     */
    public static int hashCodeModProofIrrelevancy(Operator op) {
        return Objects.hash(op.arity(), op.name());
    }

    // LocationVariable
    /**
     * test for equality modulo proof irrelevancy for the given arguments
     *
     * @param _this the first LocationVariable
     * @param that the second LocationVariable
     * @return true if both arguments are equal modulo proof irrelevancy
     */
    public static boolean equalsModProofIrrelevancy(LocationVariable _this, LocationVariable that) {
        if (_this == that) {
            return true;
        } else if (that == null || _this == null) {
            return false;
        }
        return _this.isStatic() == that.isStatic()
                && _this.isModel() == that.isModel()
                && _this.isGhost() == that.isGhost()
                && _this.isFinal() == that.isFinal()
                && equalsModProofIrrelevancy(_this.getKeYJavaType(), that.getKeYJavaType())
                && equalsModProofIrrelevancy(_this.argSorts(), that.argSorts())
                && _this.name().toString().equals(that.name().toString())
                && _this.arity() == that.arity()
                && Objects.equals(_this.whereToBind(), that.whereToBind())
                && _this.isRigid() == that.isRigid();
    }

    /**
     * Compares two {@link KeYJavaType} objects for equality based on their name
     *
     * @param thisKJT The first {@code KeYJavaType} object to compare.
     * @param thatKJT The second {@code KeYJavaType} object to compare.
     * @return {@code true} if the two {@code KeYJavaType} objects are considered equal;
     *         {@code false} otherwise.
     */
    public static boolean equalsModProofIrrelevancy(KeYJavaType thisKJT, KeYJavaType thatKJT) {
        if (thisKJT == thatKJT)
            return true;
        if (thisKJT != null && thatKJT != null) {
            if (thisKJT.getJavaType() != null &&
                    thatKJT.getJavaType() != null &&
                    thisKJT.getJavaType() instanceof SuperArrayDeclaration) {
                return thatKJT.getJavaType() instanceof SuperArrayDeclaration;
            }
            return thisKJT.getFullName().equals(thatKJT.getFullName());
        }
        return false;
    }

    /**
     * Compares two {@link Sort} objects for equality based on their name
     *
     * @param thisSort The first {@code Sort} object to compare.
     * @param thatSort The second {@code Sort} object to compare.
     * @return {@code true} if the two {@code Sort} objects are considered equal; {@code false}
     *         otherwise.
     */
    public static boolean equalsModProofIrrelevancy(Sort thisSort, Sort thatSort) {
        if (thisSort == thatSort)
            return true;
        if (thisSort != null && thatSort != null) {
            return thisSort.name().equals(thatSort.name());
        }
        return false;
    }

    /**
     * Compares two arrays of {@link Sort}s for equality based on their name
     *
     * @param thisSorts The first {@code ImmutableArray<Sort>} object to compare.
     * @param thatSorts The second {@code ImmutableArray<Sort>} object to compare.
     * @return {@code true} if the two {@code ImmutableArray<Sort>} objects are considered equal;
     *         {@code false} otherwise.
     */
    public static boolean equalsModProofIrrelevancy(ImmutableArray<Sort> thisSorts,
            ImmutableArray<Sort> thatSorts) {
        if (thisSorts == thatSorts)
            return true;
        if (thisSorts.size() != thatSorts.size())
            return false;
        for (int i = 0; i < thisSorts.size(); i++) {
            if (!thisSorts.get(i).equals(thatSorts.get(i)))
                return false;
        }
        return true;
    }


    /**
     * computes the hash code modulo proof irrelevancy for the given argument
     *
     * @param loc the LocationVariable for which to compute the hash
     * @return the hash code modulo proof irrelevancy for the given argument
     */
    public static int hashCodeModProofIrrelevancy(LocationVariable loc) {
        return Objects.hash(loc.getKeYJavaType(), loc.isStatic(), loc.isModel(), loc.isGhost(),
            loc.isFinal(), loc.sort(),
            loc.argSorts(), loc.name().toString(), loc.arity(),
            loc.whereToBind(), loc.isRigid());
    }

    // LogicVariable
    /**
     * test for equality modulo proof irrelevancy for the given arguments
     *
     * @param _this the first LogicVariable
     * @param that the second LogicVariable
     * @return true if both arguments are equal modulo proof irrelevancy
     */
    public static boolean equalsModProofIrrelevancy(LogicVariable _this, LogicVariable that) {
        if (_this == that) {
            return true;
        } else if (that == null || _this == null) {
            return false;
        }
        return _this.name().equals(that.name()) &&
                equalsModProofIrrelevancy(_this.sort(), that.sort());
    }

    /**
     * computes the hash code modulo proof irrelevancy for the given argument
     *
     * @param lv the {@link LogicVariable} for which to compute the hash
     * @return the hash code modulo proof irrelevancy for the given argument
     */
    public static int hashCodeModProofIrrelevancy(LogicVariable lv) {
        return Objects.hash(lv.name(), lv.sort());
    }


    // JavaBlock
    /**
     * test for equality modulo proof irrelevancy for the given arguments
     *
     * @param _this the first JavaBlock
     * @param that the second JavaBlock
     * @return true if both arguments are equal modulo proof irrelevancy
     */
    public static boolean equalsModProofIrrelevancy(JavaBlock _this, JavaBlock that) {
        if (_this == that) {
            return true;
        } else if (that == null || _this == null) {
            return false;
        }
        // quite inefficient, but sufficient

        // TODO: real comparison
        return equalsModProofIrrelevancy(_this.program(), that.program());
    }

    public static boolean equalsModProofIrrelevancy(ProgramElement _this, ProgramElement that) {
        if (_this == that)
            return true;
        if (that == null || _this == null)
            return false;

        if (_this.getClass() != that.getClass()) {
            return false;
        }
        if (_this instanceof TypeRef thisRef) {
            final TypeRef thatRef = (TypeRef) that;
            return thisRef.getDimensions() == thatRef.getDimensions() &&
                    equalsModProofIrrelevancy(thisRef.getProgramElementName(),
                        thatRef.getProgramElementName())
                    &&
                    equalsModProofIrrelevancy(thisRef.getReferencePrefix(),
                        thatRef.getReferencePrefix());
        } else if (_this instanceof ProgramVariable thisPV) {
            ProgramVariable thatPV = (ProgramVariable) that;
            //
            boolean sameContainerTypeName =
                equalsModProofIrrelevancy(thisPV.getContainerType(), thatPV.getContainerType());
            boolean sameTypeName =
                equalsModProofIrrelevancy(thisPV.getKeYJavaType(), thatPV.getKeYJavaType());
            return thisPV.getProgramElementName().equals(thatPV.getProgramElementName()) &&
                    sameTypeName && sameContainerTypeName;
        } else if (_this instanceof NonTerminalProgramElement thisNPE) {
            NonTerminalProgramElement thatNPE = (NonTerminalProgramElement) that;
            if (_this.getChildCount() != that.getChildCount())
                return false;
            for (int i = 0; i < _this.getChildCount(); i++) {
                if (!equalsModProofIrrelevancy(thisNPE.getChildAt(i), thatNPE.getChildAt(i))) {
                    return false;
                }
            }
            return true;
        }
        // HACK: Proper comparison needed
        return _this.toString().equals(that.toString());
    }

    /**
     * computes the hash code modulo proof irrelevancy for the given argument
     *
     * @param jb the {@link JavaBlock} for which to compute the hash
     * @return the hash code modulo proof irrelevancy for the given argument
     */
    public static int hashCodeModProofIrrelevancy(JavaBlock jb) {
        // TODO: real hashcode
        return jb.toString().hashCode();
    }

    // SequentFormula
    /**
     * test for equality modulo proof irrelevancy for the given arguments
     *
     * @param _this the first SequentFormula
     * @param that the second SequentFormula
     * @return true if both arguments are equal modulo proof irrelevancy
     */
    public static boolean equalsModProofIrrelevancy(
            SequentFormula _this,
            SequentFormula that) {
        if (_this == that) {
            return true;
        }
        if (_this != null && that != null) {
            JTerm thisFormula = (JTerm) _this.formula();
            JTerm thatFormula = (JTerm) that.formula();
            return PROOF_IRRELEVANCY_PROPERTY.equalsModThisProperty(thisFormula, thatFormula);
        }
        return false;
    }

    /**
     * computes the hash code modulo proof irrelevancy for the given argument
     *
     * @param sf the {@link SequentFormula} for which to compute the hash
     * @return the hash code modulo proof irrelevancy for the given argument
     */
    public static int hashCodeModProofIrrelevancy(
            SequentFormula sf) {
        return PROOF_IRRELEVANCY_PROPERTY.hashCodeModThisProperty((JTerm) sf.formula());
    }

    // RuleApp

    /**
     * test for equality modulo proof irrelevancy for the given arguments
     *
     * @param _this the first RuleApp
     * @param that the second RuleApp
     * @return true if both arguments are equal modulo proof irrelevancy
     */
    public static boolean equalsModProofIrrelevancy(RuleApp _this,
            RuleApp that) {
        if (_this == that) {
            return true;
        } else if (_this == null || that == null) {
            return false;
        } else if (_this.getClass() != that.getClass()) {
            return false;
        }

        if (_this instanceof TacletApp _thisTA && that instanceof TacletApp thatTA) {
            return equalsModProofIrrelevancy(_thisTA, thatTA);
        } else {
            return equalsModProofIrrelevancy((IBuiltInRuleApp) _this,
                (IBuiltInRuleApp) that);
        }
    }

    /**
     * computes the hash code modulo proof irrelevancy for the given argument
     *
     * @param app the {@link RuleApp} for which to compute the hash
     * @return the hash code modulo proof irrelevancy for the given argument
     */
    public static int hashCodeModProofIrrelevancy(RuleApp app) {
        if (app == null) {
            return 0;
        } else if (app instanceof TacletApp tApp) {
            return hashCodeModProofIrrelevancy(tApp);
        } else {
            return hashCodeModProofIrrelevancy((IBuiltInRuleApp) app);
        }

    }

    // IBuiltInRuleApp

    /**
     * test for equality modulo proof irrelevancy for the given arguments
     *
     * @param _this the first IBuiltInRuleApp
     * @param that the second IBuiltInRuleApp
     * @return true if both arguments are equal modulo proof irrelevancy
     */
    public static boolean equalsModProofIrrelevancy(IBuiltInRuleApp _this,
            IBuiltInRuleApp that) {
        if (_this == that) {
            return true;
        } else if (_this == null || that == null) {
            return false;
        }
        if (!(Objects.equals(_this.rule(), that.rule())
                && Objects.equals(_this.getHeapContext(), that.getHeapContext()))) {
            return false;
        }
        ImmutableList<PosInOccurrence> ifInsts1 = _this.assumesInsts();
        ImmutableList<PosInOccurrence> ifInsts2 = that.assumesInsts();
        if (ifInsts1.size() != ifInsts2.size()) {
            return false;
        }
        while (!ifInsts1.isEmpty()) {
            if (!ifInsts1.head().eqEquals(ifInsts2.head())) {
                return false;
            }
            ifInsts1 = ifInsts1.tail();
            ifInsts2 = ifInsts2.tail();
        }
        return _this.posInOccurrence().eqEquals(that.posInOccurrence());
    }

    /**
     * computes the hash code modulo proof irrelevancy for the given argument
     *
     * @param ruleApp the {@link IBuiltInRuleApp} for which to compute the hash
     * @return the hash code modulo proof irrelevancy for the given argument
     */
    public static int hashCodeModProofIrrelevancy(IBuiltInRuleApp ruleApp) {
        var sf = ruleApp.posInOccurrence().sequentFormula();
        return Objects.hash(ruleApp.rule(), ruleApp.getHeapContext(),
            hashCodeModProofIrrelevancy(sf),
            ruleApp.posInOccurrence().posInTerm());
    }


    // Taclet
    /**
     * test for equality modulo proof irrelevancy for the given arguments
     *
     * @param _this the first Taclet
     * @param that the second Taclet
     * @return true if both arguments are equal modulo proof irrelevancy
     */
    public static boolean equalsModProofIrrelevancy(Taclet _this, Taclet that) {
        if (that == _this)
            return true;

        if (that == null || that.getClass() != _this.getClass()) {
            return false;
        }

        if ((_this.assumesSequent() == null && that.assumesSequent() != null)
                || (_this.assumesSequent() != null && that.assumesSequent() == null)) {
            return false;
        } else {
            ImmutableList<SequentFormula> if1 =
                _this.assumesSequent().asList();
            ImmutableList<SequentFormula> if2 =
                that.assumesSequent().asList();
            while (!if1.isEmpty() && !if2.isEmpty()
                    && equalsModProofIrrelevancy(if1.head(), if2.head())) {
                if1 = if1.tail();
                if2 = if2.tail();
            }
            if (!if1.isEmpty() || !if2.isEmpty()) {
                return false;
            }
        }

        if (!_this.getChoices().equals(that.getChoices())) {
            return false;
        }

        return _this.goalTemplates().equals(that.goalTemplates());
    }

    /**
     * computes the hash code modulo proof irrelevancy for the given argument
     *
     * @param taclet the {@link Taclet} for which to compute the hash
     * @return the hash code modulo proof irrelevancy for the given argument
     */
    public static int hashCodeModProofIrrelevancy(Taclet taclet) {
        Sequent sequentFormulas = taclet.assumesSequent();
        return hashCodeModProofIrrelevancy(sequentFormulas.getFormulaByNr(1));
    }


    // TacletApp

    /**
     * test for equality modulo proof irrelevancy for the given arguments
     *
     * @param _this the first TacletApp
     * @param that the second TacletApp
     * @return true if both arguments are equal modulo proof irrelevancy
     */
    public static boolean equalsModProofIrrelevancy(TacletApp _this, TacletApp that) {
        if (_this == that) {
            return true;
        } else if (_this == null || that == null) {
            return false;
        }

        if (!EqualsModProofIrrelevancyUtil.compareImmutableLists(
            _this.assumesFormulaInstantiations(),
            that.assumesFormulaInstantiations(),
            EqualityModuloProofIrrelevancy::equalsModProofIrrelevancy)) {
            return false;
        }
        if (!equalsModProofIrrelevancy(_this.instantiations, that.instantiations)) {
            return false;
        }
        final MatchConditions matchConditions = _this.matchConditions();
        if (!equalsModProofIrrelevancy(matchConditions,
            that.matchConditions())) {
            return false;
        }
        final var missingVars = _this.uninstantiatedVars();
        final var thatMissingVars = that.uninstantiatedVars();
        if (!thatMissingVars.isEmpty()
                && !missingVars.isEmpty()
                && !Objects.equals(missingVars, thatMissingVars)) {
            return false;
        }
        return equalsModProofIrrelevancy(_this.taclet(), that.taclet());
    }

    /**
     * computes the hash code modulo proof irrelevancy for the given argument
     *
     * @param app the {@link TacletApp} for which to compute the hash
     * @return the hash code modulo proof irrelevancy for the given argument
     */
    public static int hashCodeModProofIrrelevancy(TacletApp app) {
        MatchConditions matchConditions = app.matchConditions();
        return Objects.hash(
            EqualsModProofIrrelevancyUtil.hashCodeImmutableList(app.assumesFormulaInstantiations(),
                EqualityModuloProofIrrelevancy::hashCodeModProofIrrelevancy),
            app.instantiations(),
            hashCodeModProofIrrelevancy(matchConditions),
            app.uninstantiatedVars(),
            app.isUpdateContextFixed(),
            app.rule());
    }

    // MatchConditions
    /**
     * test for equality modulo proof irrelevancy for the given arguments
     *
     * @param _this the first MatchConditions
     * @param that the second MatchConditions
     * @return true if both arguments are equal modulo proof irrelevancy
     */
    public static boolean equalsModProofIrrelevancy(MatchConditions _this, MatchConditions that) {
        if (_this == that) {
            return true;
        } else if (_this == null || that == null) {
            return false;
        }
        return equalsModProofIrrelevancy(_this.getInstantiations(), that.getInstantiations())
                && _this.renameTable().equals(that.renameTable());
    }

    /**
     * computes the hash code modulo proof irrelevancy for the given argument
     *
     * @param mc the {@link MatchConditions} for which to compute the hash
     * @return the hash code modulo proof irrelevancy for the given argument
     */
    public static int hashCodeModProofIrrelevancy(MatchConditions mc) {
        return Objects.hash(mc.getInstantiations(), mc.renameTable());
    }

    // SVInstantiation
    /**
     * test for equality modulo proof irrelevancy for the given arguments
     *
     * @param _this the first SVInstantiations
     * @param that the second SVInstantiations
     * @return true if both arguments are equal modulo proof irrelevancy
     */
    public static boolean equalsModProofIrrelevancy(SVInstantiations _this,
            SVInstantiations that) {
        if (_this == that) {
            return true;
        } else if (that == null || _this == null) {
            return false;
        }

        if (_this.size() != that.size()
                || !_this.getUpdateContext().equals(that.getUpdateContext())) {
            return false;
        }

        for (final var e : _this.getInstantiationMap()) {
            final Object inst = e.value().getInstantiation();
            if (inst instanceof JTerm instAsTerm) {
                if (!instAsTerm.equalsModProperty(
                    that.getInstantiation(e.key()), PROOF_IRRELEVANCY_PROPERTY)) {
                    return false;
                }
            } else if (inst instanceof ProgramElement instAsProgramElement) {
                if (!equalsModProofIrrelevancy(instAsProgramElement,
                    (ProgramElement) that.getInstantiation(e.key()))) {
                    return false;
                }
            } else if (!inst.equals(that.getInstantiation(e.key()))) {
                return false;
            }
        }
        return true;
    }

    /**
     * computes the hash code modulo proof irrelevancy for the given argument
     *
     * @param svInst the {@link SVInstantiations} for which to compute the hash
     * @return the hash code modulo proof irrelevancy for the given argument
     */
    public static int hashCodeModProofIrrelevancy(SVInstantiations svInst) {
        return Objects.hash(svInst.getUpdateContext(), svInst.getGenericSortConditions(),
            svInst.getExecutionContext()) + 13 * svInst.size(); // not used currently
    }

    // IFFormulaInstantiation
    /**
     * test for equality modulo proof irrelevancy for the given arguments
     *
     * @param _this the first AssumesFormulaInstantiation
     * @param that the second AssumesFormulaInstantiation
     * @return true if both arguments are equal modulo proof irrelevancy
     */
    public static boolean equalsModProofIrrelevancy(AssumesFormulaInstantiation _this,
            AssumesFormulaInstantiation that) {
        if (_this == that) {
            return true;
        } else if (that == null || _this == null) {
            return false;
        }
        return equalsModProofIrrelevancy(
            _this.getSequentFormula(), that.getSequentFormula());
    }

    /**
     * computes the hash code modulo proof irrelevancy for the given argument
     *
     * @param ifInst the {@link AssumesFormulaInstantiation} for which to compute the hash
     * @return the hash code modulo proof irrelevancy for the given argument
     */
    public static int hashCodeModProofIrrelevancy(AssumesFormulaInstantiation ifInst) {
        return hashCodeModProofIrrelevancy(ifInst.getSequentFormula());
    }
}
