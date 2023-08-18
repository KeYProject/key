/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.util.collection.ImmutableArray;

/**
 * <p>
 * This class is a specialization of {@link ProgramVariableCollector} which returns as result
 * ({@link #result()}) used {@link LocationVariable} which are undeclared, but used in the given
 * {@link ProgramElement.
 * </p>
 * <p>
 * Declared {@link LocationVariable}s are:
 * <ul>
 * <li>Local variables in blocks and methods</li>
 * <li>Self variable of an {@link ExecutionContext}</li>
 * <li>Result variable of a {@link MethodFrame}</li>
 * </ul>
 * </p>
 *
 * @author Martin Hentschel
 */
public class UndeclaredProgramVariableCollector extends ProgramVariableCollector {
    /**
     * Contains the found declared {@link IProgramVariable}s.
     */
    private final LinkedHashSet<IProgramVariable> declaredVariables =
        new LinkedHashSet<>();

    /**
     * Contains the super result.
     */
    private LinkedHashSet<LocationVariable> allVariables;

    /**
     * Contains the undeclared variables as result.
     */
    private LinkedHashSet<LocationVariable> undeclaredVariables;

    /**
     * Constructor.
     *
     * @param root The {@link ProgramElement} to collect undeclared variables in.
     * @param services The {@link Services} to use.
     */
    public UndeclaredProgramVariableCollector(ProgramElement root, Services services) {
        super(root, services);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void collectHeapVariables() {
        // Ignore heap
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void performActionOnLocalVariableDeclaration(LocalVariableDeclaration x) {
        ImmutableArray<VariableSpecification> varSpecs = x.getVariableSpecifications();
        for (VariableSpecification spec : varSpecs) {
            IProgramVariable var = spec.getProgramVariable();
            if (var != null) {
                declaredVariables.add(var);
            }
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void performActionOnMethodFrame(MethodFrame x) {
        IProgramVariable resultVar = x.getProgramVariable();
        if (resultVar != null) {
            declaredVariables.add(resultVar);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void performActionOnExecutionContext(ExecutionContext x) {
        if (x.getRuntimeInstance() instanceof IProgramVariable) {
            declaredVariables.add((IProgramVariable) x.getRuntimeInstance());
        }
    }

    /**
     * Returns the found declared variables.
     *
     * @return The found declared variables.
     */
    public Set<IProgramVariable> getDeclaredVariables() {
        return declaredVariables;
    }

    /**
     * Returns all used variables.
     *
     * @return All used variables.
     */
    public LinkedHashSet<LocationVariable> getAllVariables() {
        if (allVariables == null) {
            allVariables = super.result();
        }
        return allVariables;
    }

    /**
     * Returns the undeclared variables as result.
     *
     * @return The undeclared variables.
     */
    @Override
    public LinkedHashSet<LocationVariable> result() {
        if (undeclaredVariables == null) {
            // Create result Set
            undeclaredVariables = new LinkedHashSet<>();
            // Add all found variables
            undeclaredVariables.addAll(getAllVariables());
            // Remove all declared variables
            undeclaredVariables.removeAll(getDeclaredVariables());
            // Remove all fields (members)
            undeclaredVariables.removeIf(ProgramVariable::isMember);
        }
        return undeclaredVariables;
    }
}
