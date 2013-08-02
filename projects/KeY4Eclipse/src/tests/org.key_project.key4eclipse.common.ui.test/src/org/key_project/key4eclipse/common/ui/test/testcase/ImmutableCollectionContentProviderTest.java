/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.key4eclipse.common.ui.test.testcase;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.key4eclipse.common.ui.provider.ImmutableCollectionContentProvider;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;

/**
 * Tests for {@link ImmutableCollectionContentProvider}.
 * @author Martin Hentschel
 */
public class ImmutableCollectionContentProviderTest extends TestCase {
    /**
     * Tests the handling of {@code null}
     */
    @Test
    public void testNull() {
        Object[] result = ImmutableCollectionContentProvider.getInstance().getElements(null);
        assertEquals(0, result.length);
    }

    /**
     * Tests the handling of {@link ImmutableSet}.
     */
    @Test
    public void testImmutableSet() {
        // Test empty array
        ImmutableSet<String> input = DefaultImmutableSet.nil();
        Object[] result = ImmutableCollectionContentProvider.getInstance().getElements(input);
        assertEquals(0, result.length);
        // Test array with one element
        input = input.add("A");
        result = ImmutableCollectionContentProvider.getInstance().getElements(input);
        assertEquals(1, result.length);
        assertEquals("A", result[0]);
        // Test array with two elements
        input = input.add("B");
        result = ImmutableCollectionContentProvider.getInstance().getElements(input);
        assertEquals(2, result.length);
        assertEquals("B", result[0]);
        assertEquals("A", result[1]);
        // Test array with three elements
        input = input.add("C");
        result = ImmutableCollectionContentProvider.getInstance().getElements(input);
        assertEquals(3, result.length);
        assertEquals("C", result[0]);
        assertEquals("B", result[1]);
        assertEquals("A", result[2]);
    }
    
    /**
     * Tests the handling of {@link ImmutableList}.
     */
    @Test
    public void testImmutableList() {
        // Test empty array
        ImmutableList<String> input = ImmutableSLList.nil();
        Object[] result = ImmutableCollectionContentProvider.getInstance().getElements(input);
        assertEquals(0, result.length);
        // Test array with one element
        input = input.append("A");
        result = ImmutableCollectionContentProvider.getInstance().getElements(input);
        assertEquals(1, result.length);
        assertEquals("A", result[0]);
        // Test array with two elements
        input = input.append("B");
        result = ImmutableCollectionContentProvider.getInstance().getElements(input);
        assertEquals(2, result.length);
        assertEquals("A", result[0]);
        assertEquals("B", result[1]);
        // Test array with three elements
        input = input.append("C");
        result = ImmutableCollectionContentProvider.getInstance().getElements(input);
        assertEquals(3, result.length);
        assertEquals("A", result[0]);
        assertEquals("B", result[1]);
        assertEquals("C", result[2]);
    }
    
    /**
     * Tests the handling of {@link ImmutableArray}.
     */
    @Test
    public void testImmutableArray() {
        // Test empty array
        ImmutableArray<String> input = new ImmutableArray<String>();
        Object[] result = ImmutableCollectionContentProvider.getInstance().getElements(input);
        assertEquals(0, result.length);
        // Test array with one element
        input = new ImmutableArray<String>("A");
        result = ImmutableCollectionContentProvider.getInstance().getElements(input);
        assertEquals(1, result.length);
        assertEquals("A", result[0]);
        // Test array with two elements
        input = new ImmutableArray<String>("A", "B");
        result = ImmutableCollectionContentProvider.getInstance().getElements(input);
        assertEquals(2, result.length);
        assertEquals("A", result[0]);
        assertEquals("B", result[1]);
        // Test array with three elements
        input = new ImmutableArray<String>("A", "B", "C");
        result = ImmutableCollectionContentProvider.getInstance().getElements(input);
        assertEquals(3, result.length);
        assertEquals("A", result[0]);
        assertEquals("B", result[1]);
        assertEquals("C", result[2]);
    }
}