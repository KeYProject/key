package org.key_project.sed.ui.visualization.test.testcase;

import junit.framework.TestCase;

import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.ui.services.GraphitiUi;
import org.junit.Test;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;

/**
 * Tests for {@link GraphitiUtil}.
 * @author Martin Hentschel
 */
public class GraphitiUtilTest extends TestCase {
   /**
    * Tests {@link GraphitiUtil#nextGrid(org.eclipse.graphiti.mm.pictograms.Diagram, int)}
    */
   @Test
   public void testNextGrid() {
      // Create diagram with snap to grid
      Diagram diagramSnap = GraphitiUi.getPeService().createDiagram(ExecutionTreeDiagramTypeProvider.DIAGRAM_TYPE_ID, "Test", 5, true);
      assertNotNull(diagramSnap);
      assertEquals(5, diagramSnap.getGridUnit());
      assertTrue(diagramSnap.isSnapToGrid());
      // Create diagram without snap to grid
      Diagram diagramNoSnap = GraphitiUi.getPeService().createDiagram(ExecutionTreeDiagramTypeProvider.DIAGRAM_TYPE_ID, "Test", 5, false);
      assertNotNull(diagramNoSnap);
      assertEquals(5, diagramNoSnap.getGridUnit());
      assertFalse(diagramNoSnap.isSnapToGrid());
      // Create diagram with snap to grid and zero grid unit
      Diagram diagramZeroSnap = GraphitiUi.getPeService().createDiagram(ExecutionTreeDiagramTypeProvider.DIAGRAM_TYPE_ID, "Test", 0, true);
      assertNotNull(diagramZeroSnap);
      assertEquals(0, diagramZeroSnap.getGridUnit());
      assertTrue(diagramZeroSnap.isSnapToGrid());
      // Create diagram with snap to grid and zero grid unit
      Diagram diagramNegativeSnap = GraphitiUi.getPeService().createDiagram(ExecutionTreeDiagramTypeProvider.DIAGRAM_TYPE_ID, "Test", -5, true);
      assertNotNull(diagramNegativeSnap);
      assertEquals(-5, diagramNegativeSnap.getGridUnit());
      assertTrue(diagramNegativeSnap.isSnapToGrid());
      // test null
      assertEquals(100, GraphitiUtil.nextGrid(null, 100));
      // Test on grid with snap to grid
      assertEquals(0, GraphitiUtil.nextGrid(diagramSnap, 0));
      assertEquals(5, GraphitiUtil.nextGrid(diagramSnap, 5));
      assertEquals(95, GraphitiUtil.nextGrid(diagramSnap, 95));
      assertEquals(100, GraphitiUtil.nextGrid(diagramSnap, 100));
      assertEquals(105, GraphitiUtil.nextGrid(diagramSnap, 105));
      assertEquals(-5, GraphitiUtil.nextGrid(diagramSnap, -5));
      assertEquals(-95, GraphitiUtil.nextGrid(diagramSnap, -95));
      assertEquals(-100, GraphitiUtil.nextGrid(diagramSnap, -100));
      assertEquals(-105, GraphitiUtil.nextGrid(diagramSnap, -105));
      // Test not on grid with snap to grid
      assertEquals(5, GraphitiUtil.nextGrid(diagramSnap, 1));
      assertEquals(5, GraphitiUtil.nextGrid(diagramSnap, 2));
      assertEquals(5, GraphitiUtil.nextGrid(diagramSnap, 3));
      assertEquals(5, GraphitiUtil.nextGrid(diagramSnap, 4));
      assertEquals(100, GraphitiUtil.nextGrid(diagramSnap, 96));
      assertEquals(100, GraphitiUtil.nextGrid(diagramSnap, 97));
      assertEquals(100, GraphitiUtil.nextGrid(diagramSnap, 98));
      assertEquals(100, GraphitiUtil.nextGrid(diagramSnap, 99));
      assertEquals(105, GraphitiUtil.nextGrid(diagramSnap, 101));
      assertEquals(105, GraphitiUtil.nextGrid(diagramSnap, 102));
      assertEquals(105, GraphitiUtil.nextGrid(diagramSnap, 103));
      assertEquals(105, GraphitiUtil.nextGrid(diagramSnap, 104));
      assertEquals(-5, GraphitiUtil.nextGrid(diagramSnap, -1));
      assertEquals(-5, GraphitiUtil.nextGrid(diagramSnap, -2));
      assertEquals(-5, GraphitiUtil.nextGrid(diagramSnap, -3));
      assertEquals(-5, GraphitiUtil.nextGrid(diagramSnap, -4));
      assertEquals(-100, GraphitiUtil.nextGrid(diagramSnap, -96));
      assertEquals(-100, GraphitiUtil.nextGrid(diagramSnap, -97));
      assertEquals(-100, GraphitiUtil.nextGrid(diagramSnap, -98));
      assertEquals(-100, GraphitiUtil.nextGrid(diagramSnap, -99));
      assertEquals(-105, GraphitiUtil.nextGrid(diagramSnap, -101));
      assertEquals(-105, GraphitiUtil.nextGrid(diagramSnap, -102));
      assertEquals(-105, GraphitiUtil.nextGrid(diagramSnap, -103));
      assertEquals(-105, GraphitiUtil.nextGrid(diagramSnap, -104));
      // Test on grid without snap to grid
      assertEquals(0, GraphitiUtil.nextGrid(diagramNoSnap, 0));
      assertEquals(5, GraphitiUtil.nextGrid(diagramNoSnap, 5));
      assertEquals(95, GraphitiUtil.nextGrid(diagramNoSnap, 95));
      assertEquals(100, GraphitiUtil.nextGrid(diagramNoSnap, 100));
      assertEquals(105, GraphitiUtil.nextGrid(diagramNoSnap, 105));
      assertEquals(-5, GraphitiUtil.nextGrid(diagramNoSnap, -5));
      assertEquals(-95, GraphitiUtil.nextGrid(diagramNoSnap, -95));
      assertEquals(-100, GraphitiUtil.nextGrid(diagramNoSnap, -100));
      assertEquals(-105, GraphitiUtil.nextGrid(diagramNoSnap, -105));
      // Test not on grid without snap to grid
      assertEquals(1, GraphitiUtil.nextGrid(diagramNoSnap, 1));
      assertEquals(2, GraphitiUtil.nextGrid(diagramNoSnap, 2));
      assertEquals(3, GraphitiUtil.nextGrid(diagramNoSnap, 3));
      assertEquals(4, GraphitiUtil.nextGrid(diagramNoSnap, 4));
      assertEquals(96, GraphitiUtil.nextGrid(diagramNoSnap, 96));
      assertEquals(97, GraphitiUtil.nextGrid(diagramNoSnap, 97));
      assertEquals(98, GraphitiUtil.nextGrid(diagramNoSnap, 98));
      assertEquals(99, GraphitiUtil.nextGrid(diagramNoSnap, 99));
      assertEquals(101, GraphitiUtil.nextGrid(diagramNoSnap, 101));
      assertEquals(102, GraphitiUtil.nextGrid(diagramNoSnap, 102));
      assertEquals(103, GraphitiUtil.nextGrid(diagramNoSnap, 103));
      assertEquals(104, GraphitiUtil.nextGrid(diagramNoSnap, 104));
      assertEquals(-1, GraphitiUtil.nextGrid(diagramNoSnap, -1));
      assertEquals(-2, GraphitiUtil.nextGrid(diagramNoSnap, -2));
      assertEquals(-3, GraphitiUtil.nextGrid(diagramNoSnap, -3));
      assertEquals(-4, GraphitiUtil.nextGrid(diagramNoSnap, -4));
      assertEquals(-96, GraphitiUtil.nextGrid(diagramNoSnap, -96));
      assertEquals(-97, GraphitiUtil.nextGrid(diagramNoSnap, -97));
      assertEquals(-98, GraphitiUtil.nextGrid(diagramNoSnap, -98));
      assertEquals(-99, GraphitiUtil.nextGrid(diagramNoSnap, -99));
      assertEquals(-101, GraphitiUtil.nextGrid(diagramNoSnap, -101));
      assertEquals(-102, GraphitiUtil.nextGrid(diagramNoSnap, -102));
      assertEquals(-103, GraphitiUtil.nextGrid(diagramNoSnap, -103));
      assertEquals(-104, GraphitiUtil.nextGrid(diagramNoSnap, -104));
      // Test on grid with snap to grid and a grid size of zero
      assertEquals(0, GraphitiUtil.nextGrid(diagramZeroSnap, 0));
      assertEquals(5, GraphitiUtil.nextGrid(diagramZeroSnap, 5));
      assertEquals(95, GraphitiUtil.nextGrid(diagramZeroSnap, 95));
      assertEquals(100, GraphitiUtil.nextGrid(diagramZeroSnap, 100));
      assertEquals(105, GraphitiUtil.nextGrid(diagramZeroSnap, 105));
      assertEquals(-5, GraphitiUtil.nextGrid(diagramZeroSnap, -5));
      assertEquals(-95, GraphitiUtil.nextGrid(diagramZeroSnap, -95));
      assertEquals(-100, GraphitiUtil.nextGrid(diagramZeroSnap, -100));
      assertEquals(-105, GraphitiUtil.nextGrid(diagramZeroSnap, -105));
      // Test not on grid without snap to grid and a grid size of zero
      assertEquals(1, GraphitiUtil.nextGrid(diagramZeroSnap, 1));
      assertEquals(2, GraphitiUtil.nextGrid(diagramZeroSnap, 2));
      assertEquals(3, GraphitiUtil.nextGrid(diagramZeroSnap, 3));
      assertEquals(4, GraphitiUtil.nextGrid(diagramZeroSnap, 4));
      assertEquals(96, GraphitiUtil.nextGrid(diagramZeroSnap, 96));
      assertEquals(97, GraphitiUtil.nextGrid(diagramZeroSnap, 97));
      assertEquals(98, GraphitiUtil.nextGrid(diagramZeroSnap, 98));
      assertEquals(99, GraphitiUtil.nextGrid(diagramZeroSnap, 99));
      assertEquals(101, GraphitiUtil.nextGrid(diagramZeroSnap, 101));
      assertEquals(102, GraphitiUtil.nextGrid(diagramZeroSnap, 102));
      assertEquals(103, GraphitiUtil.nextGrid(diagramZeroSnap, 103));
      assertEquals(104, GraphitiUtil.nextGrid(diagramZeroSnap, 104));
      assertEquals(-1, GraphitiUtil.nextGrid(diagramZeroSnap, -1));
      assertEquals(-2, GraphitiUtil.nextGrid(diagramZeroSnap, -2));
      assertEquals(-3, GraphitiUtil.nextGrid(diagramZeroSnap, -3));
      assertEquals(-4, GraphitiUtil.nextGrid(diagramZeroSnap, -4));
      assertEquals(-96, GraphitiUtil.nextGrid(diagramZeroSnap, -96));
      assertEquals(-97, GraphitiUtil.nextGrid(diagramZeroSnap, -97));
      assertEquals(-98, GraphitiUtil.nextGrid(diagramZeroSnap, -98));
      assertEquals(-99, GraphitiUtil.nextGrid(diagramZeroSnap, -99));
      assertEquals(-101, GraphitiUtil.nextGrid(diagramZeroSnap, -101));
      assertEquals(-102, GraphitiUtil.nextGrid(diagramZeroSnap, -102));
      assertEquals(-103, GraphitiUtil.nextGrid(diagramZeroSnap, -103));
      assertEquals(-104, GraphitiUtil.nextGrid(diagramZeroSnap, -104));
      // Test on grid with snap to grid and a negative grid size
      assertEquals(0, GraphitiUtil.nextGrid(diagramNegativeSnap, 0));
      assertEquals(5, GraphitiUtil.nextGrid(diagramNegativeSnap, 5));
      assertEquals(95, GraphitiUtil.nextGrid(diagramNegativeSnap, 95));
      assertEquals(100, GraphitiUtil.nextGrid(diagramNegativeSnap, 100));
      assertEquals(105, GraphitiUtil.nextGrid(diagramNegativeSnap, 105));
      assertEquals(-5, GraphitiUtil.nextGrid(diagramNegativeSnap, -5));
      assertEquals(-95, GraphitiUtil.nextGrid(diagramNegativeSnap, -95));
      assertEquals(-100, GraphitiUtil.nextGrid(diagramNegativeSnap, -100));
      assertEquals(-105, GraphitiUtil.nextGrid(diagramNegativeSnap, -105));
      // Test not on grid with snap to grid and a negative grid size
      assertEquals(5, GraphitiUtil.nextGrid(diagramNegativeSnap, 1));
      assertEquals(5, GraphitiUtil.nextGrid(diagramNegativeSnap, 2));
      assertEquals(5, GraphitiUtil.nextGrid(diagramNegativeSnap, 3));
      assertEquals(5, GraphitiUtil.nextGrid(diagramNegativeSnap, 4));
      assertEquals(100, GraphitiUtil.nextGrid(diagramNegativeSnap, 96));
      assertEquals(100, GraphitiUtil.nextGrid(diagramNegativeSnap, 97));
      assertEquals(100, GraphitiUtil.nextGrid(diagramNegativeSnap, 98));
      assertEquals(100, GraphitiUtil.nextGrid(diagramNegativeSnap, 99));
      assertEquals(105, GraphitiUtil.nextGrid(diagramNegativeSnap, 101));
      assertEquals(105, GraphitiUtil.nextGrid(diagramNegativeSnap, 102));
      assertEquals(105, GraphitiUtil.nextGrid(diagramNegativeSnap, 103));
      assertEquals(105, GraphitiUtil.nextGrid(diagramNegativeSnap, 104));
      assertEquals(-5, GraphitiUtil.nextGrid(diagramNegativeSnap, -1));
      assertEquals(-5, GraphitiUtil.nextGrid(diagramNegativeSnap, -2));
      assertEquals(-5, GraphitiUtil.nextGrid(diagramNegativeSnap, -3));
      assertEquals(-5, GraphitiUtil.nextGrid(diagramNegativeSnap, -4));
      assertEquals(-100, GraphitiUtil.nextGrid(diagramNegativeSnap, -96));
      assertEquals(-100, GraphitiUtil.nextGrid(diagramNegativeSnap, -97));
      assertEquals(-100, GraphitiUtil.nextGrid(diagramNegativeSnap, -98));
      assertEquals(-100, GraphitiUtil.nextGrid(diagramNegativeSnap, -99));
      assertEquals(-105, GraphitiUtil.nextGrid(diagramNegativeSnap, -101));
      assertEquals(-105, GraphitiUtil.nextGrid(diagramNegativeSnap, -102));
      assertEquals(-105, GraphitiUtil.nextGrid(diagramNegativeSnap, -103));
      assertEquals(-105, GraphitiUtil.nextGrid(diagramNegativeSnap, -104));
   }
}
