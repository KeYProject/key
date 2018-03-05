package de.uka.ilkd.key.speclang;

import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.InfFlowSpec;

/**
 * <p> A contract for a block that begins with a loop. </p>
 * 
 * <p>
 *  When a loop contract is encountered in an existing proof, a {@code LoopContract} is used.
 *  To generate a new proof obligation for a block contract, use {@link FunctionalLoopContract}
 *  instead.
 * </p>
 * 
 */
public interface LoopContract extends BlockSpecificationElement {

    /**
     * 
     * @return all {@link FunctionalLoopContract}s with a valid id that correspond to this
     *  {@code LoopContract}. Unless this contract is a combination of other contracts
     *  (see {@link SimpleLoopContract#combine(ImmutableSet, Services)}, the resulting set
     *  will only contain one element.
     */
    public ImmutableSet<FunctionalLoopContract> getFunctionalContracts();
    
    /**
     * 
     * @param contract
     * @see #getFunctionalContracts()
     */
    public void setFunctionalLoopContract(FunctionalLoopContract contract);

	public Term getDecreases();
	public Term getDecreases(Variables variables, Services services);
    
    public LoopContract setTarget(KeYJavaType newKJT, IObserverFunction newPM);
    public LoopContract setBlock(StatementBlock newBlock);


    public Expression getGuard();
    public StatementBlock getBody();
    public StatementBlock getTail();

    public While getLoop();
    
    public List<Label> getLoopLabels();

    LoopContract update(StatementBlock newBlock,
            Map<LocationVariable, Term> newPreconditions,
            Map<LocationVariable, Term> newPostconditions,
            Map<LocationVariable, Term> newModifiesClauses,
            ImmutableList<InfFlowSpec> newinfFlowSpecs, Variables newVariables,
            Term newMeasuredBy, Term newDecreases);
}
