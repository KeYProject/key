package org.key_project.sed.key.core.launch.key.po;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.util.MiscTools;

/**
 * <p>
 * This class extends the functionality of {@link FunctionalOperationContract}
 * for the special purpose of the Symbolic Execution Debugger.
 * </p>
 * <p>
 * The difference to created proof obligations of {@link FunctionalOperationContract}
 * is that the post condition is enriched by an extra non-rigid predicate of
 * form {@code predicate SEDAccumulate(HeapSort, MethodParameter1Sort, ... MethodParameterNSort)}. 
 * </p>
 * <p>
 * The extra predicate is used for two purposes:
 * <ul>
 *    <li>The proof is not closeable. This is a required functionality of
 *        the Symbolic Execution Debugger to filter invalid execution paths.
 *        Such invalid paths are closed branches in the proof tree.
 *        Only open branches are possible execution trees.</li>
 *    <li>The predicate parameters protects the parameters to be removed
 *        by the proof strategy but it is still allowed to remove
 *        variables not interested in (all the others wich are no parameter of the predicate)</li>
 * </ul>
 * </p>
 * @author Martin Hentschel
 */
public class SEDFunctionalOperationContractPO extends FunctionalOperationContractPO {
    /**
     * Constructor.
     * @param initConfig The {@link InitConfig} to use.
     * @param contract The {@link FunctionalOperationContract} to prove.
     */
    public SEDFunctionalOperationContractPO(InitConfig initConfig, 
                                            FunctionalOperationContract contract) {
        super(initConfig, contract);
    }
    
    /**
     * <p>
     * {@inheritDoc}
     * </p>
     * <p>
     * The methods adds to the post condition of the original proof obligation
     * created by the super class an extra predicate called 
     * "SEDAccumulate" which is used to filter invalid execution branches
     * in the proof tree. For more details read the class comment.
     * </p>
     */
    @Override
    protected Term buildProgramTerm(ImmutableList<ProgramVariable> paramVars,
                                    ProgramVariable selfVar,
                                    ProgramVariable resultVar,
                                    ProgramVariable exceptionVar,
                                    LocationVariable heapAtPreVar,
                                    LocationVariable savedHeapAtPreVar,
                                    Term postTerm) {
        // Create parameters for predicate SEDAccumulate(HeapSort, MethodParameter1Sort, ... MethodParameterNSort) 
        ImmutableList<Term> arguments = TermBuilder.DF.var(paramVars); // Method parameters
        arguments = arguments.prepend(TermBuilder.DF.heap(services)); // Heap (As first argument for the predicate)
        // Create non-rigid predicate with signature: SEDAccumulate(HeapSort, MethodParameter1Sort, ... MethodParameterNSort)
        ImmutableList<Sort> argumentSorts = MiscTools.getSorts(arguments);//.prepend(heapSort);
        Function f = new Function(new Name(TermBuilder.DF.newName(services, "SEDAccumulate")), 
                                  Sort.FORMULA, 
                                  argumentSorts.toArray(new Sort[argumentSorts.size()]));
        services.getNamespaces().functions().addSafely(f);
        // Create term that uses the new predicate
        Term postSubstitute = TermBuilder.DF.func(f, arguments.toArray(new Term[arguments.size()]));
        // Enrich post condition with the new predicate
        Term extendedPostTerm = TermBuilder.DF.and(postTerm, postSubstitute);
        return super.buildProgramTerm(paramVars, selfVar, resultVar, exceptionVar, heapAtPreVar, savedHeapAtPreVar, extendedPostTerm);
    }
}
