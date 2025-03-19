/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.loopinvgen;

import java.awt.*;
import java.lang.reflect.Method;
import javax.swing.*;

public class TestCaseRunner extends JFrame {
    private final JComboBox<String> testCaseComboBox;
    private final JCheckBox relaxedCheckBox;
    private final JTextArea outputTextArea;
    private static final TestPredicateConstruction tpc = new TestPredicateConstruction();

    public TestCaseRunner() {
        setTitle("Test Case Runner");
        setSize(400, 500);
        setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        setLocationRelativeTo(null);

        // Create UI components
        testCaseComboBox = new JComboBox<>(new String[] {
            "onlyRead",
            "withoutFunc",
            "withFunc",
            "intaDepOnly",
            "shiftArrayToLeft",
            "interAndIntra",
            "condition",
            "conditionDifferentNumberOfEvents",
            "conditionWithDifferentEvents0",
            "conditionWithDifferentEvents",
            "shiftArrayToLeftWithBreak",
            "stencil",
            "indexToPowerOf2",
            "basicEx0",
            "basicMltpArrDiffIndex",
            "basicMDArray0",
            "basicMDArray",
            "basicMDArray42",
            "correlation_init_array",
            "correlation_print_array",
            "gem_ver_scope_1",
            "three_nested_loops"
        });
        relaxedCheckBox = new JCheckBox("Relaxed");
        JButton runButton = new JButton("Run Test");
        outputTextArea = new JTextArea(8, 30);
        outputTextArea.setEditable(false);

        // Set up layout
        JPanel inputPanel = new JPanel();
        inputPanel.setLayout(new GridLayout(3, 1));
        inputPanel.add(testCaseComboBox);
        inputPanel.add(relaxedCheckBox);
        inputPanel.add(runButton);

        JPanel outputPanel = new JPanel();
        outputPanel.setLayout(new BorderLayout());
        outputPanel.add(new JLabel("Output:"), BorderLayout.NORTH);
        outputPanel.add(new JScrollPane(outputTextArea), BorderLayout.CENTER);

        getContentPane().setLayout(new BorderLayout());
        getContentPane().add(inputPanel, BorderLayout.NORTH);
        getContentPane().add(outputPanel, BorderLayout.CENTER);

        // Button action listener
        runButton.addActionListener(e -> runTest());
    }

    private void runTest() {
        String selectedTestCase = (String) testCaseComboBox.getSelectedItem();
        boolean relaxed = relaxedCheckBox.isSelected();

        String output = executeTest(selectedTestCase, relaxed);

        outputTextArea.setText(output);
    }

    private static String executeTest(String testCase, boolean relaxed) {
        String relaxedText = relaxed ? " (relaxed)" : "";
        String result = "Output of " + testCase + relaxedText + ": " + System.lineSeparator()
            + System.lineSeparator();

        long timeTaken = -1;
        try {
            Method test = tpc.getClass().getMethod(testCase, boolean.class);

            long start = System.currentTimeMillis();
            result += test.invoke(tpc, relaxed).toString();
            long end = System.currentTimeMillis();
            timeTaken = end - start;
        } catch (NoSuchMethodException e) {
            try {
                Method test = tpc.getClass().getMethod(testCase);

                // don't show relaxed if there is no relaxed version to run
                result = result.replace(" (relaxed)", "");

                long start = System.currentTimeMillis();
                result += test.invoke(tpc).toString();
                long end = System.currentTimeMillis();
                timeTaken = end - start;
            } catch (NoSuchMethodException e2) {
                System.out.println("No such testcase: " + testCase);
            } catch (Exception e2) {
                e.printStackTrace();
            }
        } catch (Exception e) {
            e.printStackTrace();
        }

        if (timeTaken != -1) {
            result += System.lineSeparator() + System.lineSeparator()
                + "Loop Invariant Generation took " + timeTaken + " ms";
        } else {
            result += "Encountered an error while executing this test case";
        }
        return result;
    }

    public static void main(String[] args) {
        SwingUtilities.invokeLater(() -> new TestCaseRunner().setVisible(true));
    }
}
