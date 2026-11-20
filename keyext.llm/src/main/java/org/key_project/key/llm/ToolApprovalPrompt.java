/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.Component;
import java.awt.Dialog;
import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JPanel;

import org.jspecify.annotations.Nullable;

/**
 * The user decision for a tool call that requires approval — the same three choices the chat's
 * approval box offers. Used by the {@link ToolConsoleDialog} so that tests can record decisions
 * instead of opening dialogs.
 *
 * @author Alexander Weigl
 */
public interface ToolApprovalPrompt {

    /** The decisions of an approval prompt, mirroring the chat's approval box. */
    enum Decision {
        /** Run this single call. */
        ALLOW_ONCE,
        /** Run the call and remember the tool as approved (persisted in the settings). */
        ALWAYS,
        /** Do not run the call. */
        DENY
    }

    /**
     * Asks the user whether the tool call may run.
     *
     * @param toolName the name of the tool to be called
     * @param arguments the arguments JSON document of the call
     * @return the user's decision; never {@code null}
     */
    Decision ask(String toolName, String arguments);

    /**
     * The default prompt: a modal dialog showing the tool name and arguments with the buttons
     * <em>Allow once</em>, <em>Always allow</em> and <em>Deny</em>, mirroring the chat's
     * approval box.
     */
    class Modal implements ToolApprovalPrompt {

        /** The owner of the modal dialog ({@code null} creates an owner-less dialog). */
        private final @Nullable Component owner;

        /** Creates the modal prompt with the given dialog owner. */
        public Modal(@Nullable Component owner) {
            this.owner = owner;
        }

        @Override
        public Decision ask(String toolName, String arguments) {
            var dialog = new JDialog(owner instanceof Dialog d ? d : null,
                "Approval required", Dialog.ModalityType.APPLICATION_MODAL);
            var content = new JPanel(new java.awt.BorderLayout(8, 8));
            content.setBorder(BorderFactory.createEmptyBorder(10, 12, 10, 12));
            var label = new JLabel("<html><b>Approval required:</b> tool <code>"
                + escape(toolName) + "</code><br/><code>" + escape(arguments) + "</code></html>");
            label.setBorder(BorderFactory.createEmptyBorder(0, 0, 8, 0));
            content.add(label, java.awt.BorderLayout.NORTH);

            var buttons = new JPanel(new java.awt.FlowLayout(java.awt.FlowLayout.RIGHT, 6, 0));
            var decision = new Decision[1];
            var allowOnce = new JButton("Allow once");
            allowOnce.addActionListener(e -> {
                decision[0] = Decision.ALLOW_ONCE;
                dialog.dispose();
            });
            buttons.add(allowOnce);
            var always = new JButton("Always allow");
            always.setToolTipText(
                "Remember the decision for this tool (persisted in the settings)");
            always.addActionListener(e -> {
                decision[0] = Decision.ALWAYS;
                dialog.dispose();
            });
            buttons.add(always);
            var deny = new JButton("Deny");
            deny.addActionListener(e -> {
                decision[0] = Decision.DENY;
                dialog.dispose();
            });
            buttons.add(deny);
            content.add(buttons, java.awt.BorderLayout.SOUTH);
            dialog.getRootPane().setDefaultButton(allowOnce);
            dialog.setContentPane(content);
            dialog.getRootPane().registerKeyboardAction(e -> dialog.dispose(),
                javax.swing.KeyStroke.getKeyStroke(java.awt.event.KeyEvent.VK_ESCAPE, 0),
                javax.swing.JComponent.WHEN_IN_FOCUSED_WINDOW);
            dialog.pack();
            dialog.setLocationRelativeTo(owner);
            dialog.setVisible(true);
            return decision[0] == null ? Decision.DENY : decision[0];
        }

        private static String escape(String s) {
            return (s == null ? "" : s).replace("&", "&amp;").replace("<", "&lt;")
                    .replace(">", "&gt;");
        }
    }
}
