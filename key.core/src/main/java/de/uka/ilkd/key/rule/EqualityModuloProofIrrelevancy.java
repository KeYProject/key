/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.lang.reflect.InvocationTargetException;
import java.util.Iterator;
import java.util.Objects;

import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.EqualsModProofIrrelevancyUtil;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMapEntry;

import static de.uka.ilkd.key.logic.equality.ProofIrrelevancyProperty.PROOF_IRRELEVANCY_PROPERTY;

public class EqualityModuloProofIrrelevancy {

    // Dynamic dispatch on type of _this via reflection

    public static boolean equalsModProofIrrelevancy(Object _this, Object that) {
        if (_this.getClass() == that.getClass()) {
            try {
                var method = EqualityModuloProofIrrelevancy.class.getDeclaredMethod(
                    "equalsModProofIrrelevancy",
                    _this.getClass(), that.getClass());
                return (boolean) method.invoke(null, _this, that);
            } catch (NoSuchMethodException e) {
                throw new RuntimeException(
                    "No equality modulo proof irrelevancy defined for " + _this.getClass(), e);
            } catch (IllegalAccessException | InvocationTargetException e) {
                throw new RuntimeException(
                    "No equality modulo proof irrelevancy defined for " + _this.getClass(), e);
            }
        }
        return false;
    }

    public static int hashCodeModProofIrrelevancy(Object obj) {
        try {
            var method = EqualityModuloProofIrrelevancy.class.getDeclaredMethod(
                "hashCodeModProofIrrelevancy",
                obj.getClass());
            return (int) method.invoke(null, obj);
        } catch (NoSuchMethodException e) {
            throw new RuntimeException(
                "No hash modulo proof irrelevancy defined for " + obj.getClass(), e);
        } catch (IllegalAccessException | InvocationTargetException e) {
            throw new RuntimeException(
                "No hash modulo proof irrelevancy defined for " + obj.getClass(), e);
        }
    }


    // RuleApp
    public static boolean equalsModProofIrrelevancy(RuleApp _this, RuleApp that) {
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
    public static boolean equalsModProofIrrelevancy(IBuiltInRuleApp thisRule,
            IBuiltInRuleApp thatRule) {
        if (thisRule == thatRule) {
            return true;
        } else if (thisRule == null || thatRule == null) {
            return false;
        }
        if (!(Objects.equals(thisRule.rule(), thatRule.rule())
                && Objects.equals(thisRule.getHeapContext(), thatRule.getHeapContext()))) {
            return false;
        }
        ImmutableList<PosInOccurrence> ifInsts1 = thisRule.ifInsts();
        ImmutableList<PosInOccurrence> ifInsts2 = thatRule.ifInsts();
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
        return thisRule.posInOccurrence().eqEquals(thatRule.posInOccurrence());
    }

    public static int hashCodeModProofIrrelevancy(IBuiltInRuleApp ruleApp) {
        var sf = (de.uka.ilkd.key.logic.SequentFormula) ruleApp.posInOccurrence().sequentFormula();
        return Objects.hash(ruleApp.rule(), ruleApp.getHeapContext(),
            hashCodeModProofIrrelevancy(sf),
            ruleApp.posInOccurrence().posInTerm());
    }


    // SequentFormula
    public static boolean equalsModProofIrrelevancy(SequentFormula thisSF, SequentFormula thatSF) {
        if (thisSF == thatSF) {
            return true;
        }
        if (thisSF != null && thatSF != null) {
            return thisSF.formula().equalsModProperty(thatSF.formula(), PROOF_IRRELEVANCY_PROPERTY);
        }
        return false;
    }

    public static int hashCodeModProofIrrelevancy(SequentFormula sf) {
        return sf.formula().hashCodeModProperty(PROOF_IRRELEVANCY_PROPERTY);
    }

    // Taclet

    public static boolean equalsModProofIrrelevancy(TacletApp _this, TacletApp that) {
        if (_this == that) {
            return true;
        } else if (_this == null || that == null) {
            return false;
        }

        if (!EqualsModProofIrrelevancyUtil.compareImmutableLists(_this.ifFormulaInstantiations(),
            that.ifFormulaInstantiations(),
            EqualityModuloProofIrrelevancy::equalsModProofIrrelevancy)) {
            return false;
        }
        if (!equalsModProofIrrelevancy(_this.instantiations, that.instantiations)) {
            return false;
        }
        MatchConditions matchConditions = _this.matchConditions();
        Object obj = that.matchConditions();
        if (!EqualityModuloProofIrrelevancy.equalsModProofIrrelevancy(matchConditions,
            (MatchConditions) obj)) {
            return false;
        }
        final var missingVars = _this.uninstantiatedVars();
        final var thatMissingVars = that.uninstantiatedVars();
        if ((missingVars != null || !thatMissingVars.isEmpty())
                && (!missingVars.isEmpty() || thatMissingVars != null)
                && !Objects.equals(missingVars, thatMissingVars)) {
            return false;
        }
        if (!equalsModProofIrrelevancy(_this.taclet(), that.taclet())) {
            return false;
        }
        return true;
    }

    public static int hashCodeModProofIrrelevancy(TacletApp app) {
        MatchConditions matchConditions = app.matchConditions();
        return Objects.hash(
            EqualsModProofIrrelevancyUtil.hashCodeImmutableList(app.ifFormulaInstantiations(),
                EqualityModuloProofIrrelevancy::hashCodeModProofIrrelevancy),
            app.instantiations(),
            EqualityModuloProofIrrelevancy.hashCodeModProofIrrelevancy(matchConditions),
            app.uninstantiatedVars(),
            app.isUpdateContextFixed(),
            app.rule());
    }

    // MatchConditions
    public static boolean equalsModProofIrrelevancy(MatchConditions _this, MatchConditions that) {
        if (_this == that) {
            return true;
        } else if (_this == null || that == null) {
            return false;
        }
        return equalsModProofIrrelevancy(_this.getInstantiations(), that.getInstantiations())
                && _this.renameTable().equals(that.renameTable());
    }

    public static int hashCodeModProofIrrelevancy(MatchConditions mc) {
        return Objects.hash(mc.getInstantiations(), mc.renameTable());
    }


    // Taclet
    public static boolean equalsModProofIrrelevancy(Taclet _this, Taclet that) {
        if (that == _this)
            return true;

        if (that == null || that.getClass() != _this.getClass()) {
            return false;
        }

        if ((_this.ifSequent() == null && that.ifSequent() != null)
                || (_this.ifSequent() != null && that.ifSequent() == null)) {
            return false;
        } else {
            ImmutableList<SequentFormula> if1 = _this.ifSequent().asList();
            ImmutableList<SequentFormula> if2 = that.ifSequent().asList();
            while (!if1.isEmpty() && !if2.isEmpty()
                    && equalsModProofIrrelevancy(if1.head(), if2.head())) {
                if1 = if1.tail();
                if2 = if2.tail();
            }
            if (!if1.isEmpty() || !if2.isEmpty()) {
                return false;
            }
        }

        if (!_this.choices.equals(that.choices)) {
            return false;
        }

        if (!_this.goalTemplates().equals(that.goalTemplates())) {
            return false;
        }

        return true;
    }

    public static int hashCodeModProofIrrelevancy(Taclet taclet) {
        return EqualityModuloProofIrrelevancy
                .hashCodeModProofIrrelevancy(taclet.ifSequent().getFormulabyNr(1));
    }



    // LogicVariable

    public static boolean equalsModProofIrrelevancy(LogicVariable _this, LogicVariable that) {
        if (_this == that) {
            return true;
        } else if (that == null || _this == null) {
            return false;
        }
        return _this.name().equals(that.name()) && _this.sort().equals(that.sort());
    }

    public static int hashCodeModProofIrrelevancy(LogicVariable lv) {
        return Objects.hash(lv.name(), lv.sort());
    }


    // JavaBlock

    public static boolean equalsModProofIrrelevancy(JavaBlock _this, JavaBlock that) {
        if (_this == that) {
            return true;
        } else if (that == null || _this == null) {
            return false;
        }
        // quite inefficient, but sufficient
        // TODO: real comparison
        return _this.toString().equals(that.toString());
    }

    public static int hashCodeModProofIrrelevancy(JavaBlock jb) {
        // TODO: real hashcode
        return jb.toString().hashCode();
    }

    // LocationVariable
    public static boolean equalsModProofIrrelevancy(LocationVariable _this, LocationVariable that) {
        if (_this == that) {
            return true;
        } else if (that == null || _this == null) {
            return false;
        }
        return Objects.equals(_this.getKeYJavaType(), that.getKeYJavaType())
                && _this.isStatic() == that.isStatic()
                && _this.isModel() == that.isModel()
                && _this.isGhost() == that.isGhost()
                && _this.isFinal() == that.isFinal()
                && _this.sort().equals(that.sort())
                && Objects.equals(_this.argSorts(), that.argSorts())
                && _this.name().toString().equals(that.name().toString())
                && _this.arity() == that.arity()
                && Objects.equals(_this.whereToBind(), that.whereToBind())
                && _this.isRigid() == that.isRigid();
    }

    public static int hashCodeModProofIrrelevancy(LocationVariable loc) {
        return Objects.hash(loc.getKeYJavaType(), loc.isStatic(), loc.isModel(), loc.isGhost(),
            loc.isFinal(), loc.sort(),
            loc.argSorts(), loc.name().toString(), loc.arity(),
            loc.whereToBind(), loc.isRigid());
    }

    // Operator

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
        }

        // assume name and arity uniquely identifies operator
        return _this.arity() == that.arity() && _this.name().equals(that.name());
    }

    public static int hashCodeModProofIrrelevancy(Operator op) {
        return Objects.hash(op.arity(), op.name());
    }


    // SVInstantiation

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

        final Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>>> it =
            _this.pairIterator();
        while (it.hasNext()) {
            final ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> e = it.next();
            final Object inst = e.value().getInstantiation();
            assert inst != null : "Illegal null instantiation.";
            if (inst instanceof Term instAsTerm) {
                if (!instAsTerm.equalsModProperty(
                    that.getInstantiation(e.key()), PROOF_IRRELEVANCY_PROPERTY)) {
                    return false;
                }
            } else if (!inst.equals(that.getInstantiation(e.key()))) {
                return false;
            }
        }
        return true;

    }

    public static int hashCodeModProofIrrelevancy(SVInstantiations svInst) {
        return Objects.hash(svInst.getUpdateContext(), svInst.getGenericSortConditions(),
            svInst.getExecutionContext()) + 13 * svInst.size(); // not used currently
    }

    // IFFormulaInstantiation

    public static boolean equalsModProofIrrelevancy(IfFormulaInstantiation _this,
            IfFormulaInstantiation that) {
        if (_this == that) {
            return true;
        } else if (that == null || _this == null) {
            return false;
        }
        return EqualityModuloProofIrrelevancy.equalsModProofIrrelevancy(
            _this.getConstrainedFormula(), that.getConstrainedFormula());
    }

    public static int hashCodeModProofIrrelevancy(IfFormulaInstantiation ifInst) {
        return EqualityModuloProofIrrelevancy
                .hashCodeModProofIrrelevancy(ifInst.getConstrainedFormula());
    }


}
