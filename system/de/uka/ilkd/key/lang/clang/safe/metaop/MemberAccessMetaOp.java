package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.common.program.expression.operator.MemberReference;
import de.uka.ilkd.key.lang.clang.common.sort.object.IStructuredSort;
import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.sort.object.MemberFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.StructuredSort;
import de.uka.ilkd.key.lang.common.metaop.MetaOpProgramElementSymbol;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that applies function <code>T::{member.id}</code> to its
 * first argument of CDL structured sort T and takes the member id from its
 * second argument of CDL member operator.
 * 
 * @author oleg.myrk@gmail.com
 */
public class MemberAccessMetaOp extends SafeBaseMetaOp {

        public MemberAccessMetaOp() {
                super(new Name("#ClangMemberAccess"), 2);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangSafeEnvironment context) {
                Term term0 = term.sub(0);
                Operator op1 = term.sub(1).op();
                if (!(term0.sort() instanceof IStructuredSort))
                        throw new RuntimeException(
                                        "#ClangMemberAccess applied to a term of non-structured sort");
                if (!(op1 instanceof MetaOpProgramElementSymbol && ((MetaOpProgramElementSymbol)op1).getContents() instanceof MemberReference))
                        throw new RuntimeException(
                                        "#ClangMemberAccess applied to the second argument that is not a member operator");

                StructuredSort structuredSort = ((StructuredSort) term0.sort());
                MemberReference memberReference = (MemberReference)((MetaOpProgramElementSymbol)op1).getContents();
                if (memberReference.getContainerTypePair().getSort() != term0.sort())
                        throw new RuntimeException(
                                        "#ClangMemberAccess applied to a structured sort \""
                                                        + term0.sort().name()
                                                        + "\" and a member of a different structured sort \""
                                                        + memberReference
                                                                        .getContainerTypePair()
                                                                        .getSort()
                                                                        .name()
                                                        + "\"");

                MemberFunction memberFunction = structuredSort
                                .getMemberFunctionMap().get(
                                                memberReference.getMemberName().toString());
                if (memberFunction == null)
                        throw new RuntimeException(
                                        "#ClangMemberAccess could not find member \""
                                                        + memberReference.getMemberName()
                                                        + "\" in structured sort \""
                                                        + structuredSort.name()
                                                        + "\"");

                return TermFactory.DEFAULT.createFunctionTerm(memberFunction,
                                term0);
        }
}
