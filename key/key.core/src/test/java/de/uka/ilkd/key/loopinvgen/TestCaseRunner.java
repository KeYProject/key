package de.uka.ilkd.key.loopinvgen;

import javax.swing.*;
import java.awt.*;
import java.lang.reflect.Method;

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
        testCaseComboBox = new JComboBox<>(new String[]{
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
                "correlation_init_array",
                "correlation_print_array",
                "gem_ver_scope_1"
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
        boolean isRelaxed = relaxedCheckBox.isSelected();

        // Run the test case
        String output = executeTest(selectedTestCase, isRelaxed);

        // Display the output in the text area
        outputTextArea.setText(output);
    }

    private static String executeTest(String testCase, boolean relaxed) {
        String relaxedText = relaxed ? " (relaxed)" : "";
        String result = "Output of " + testCase + relaxedText + ": " + System.lineSeparator() + System.lineSeparator();

        String fullTestName = testCase;
        if (relaxed) {
            //TODO: ???????
        }

        try {
            Method test = tpc.getClass().getMethod(fullTestName);
            result += test.invoke(tpc).toString();
        } catch (NoSuchMethodException e) {
            System.out.println("No such testcase: " + testCase);
        } catch (Exception e) {
            e.printStackTrace();
        }

        return result;
    }

    public static void main(String[] args) {
        SwingUtilities.invokeLater(() -> new TestCaseRunner().setVisible(true));
    }
}