/*******************************************************************************
 * Copyright (c) 2004 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials 
 * are made available under the terms of the Common Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/cpl-v10.html
 * 
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.jdt.core.tests.dom;

import org.eclipse.jdt.core.compiler.CharOperation;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.tests.model.ModifyingResourceTests;


public class AbstractASTTests extends ModifyingResourceTests {

	public AbstractASTTests(String name) {
		super(name);
	}
	
	/*
	 * Removes the *start* and *end* markers from the given source
	 * and remembers the positions.
	 */
	public class MarkerInfo {
		String path;
		String source;
		int astStart, astEnd;
		
		public MarkerInfo(String source) {
			this(null, source);
		}
		public MarkerInfo(String path, String source) {
			this.path = path;
			this.source = source;
			String markerStart = "/*start*/";
			String markerEnd = "/*end*/";
			this.astStart = source.indexOf(markerStart); // start of AST inclusive
			this.source = new String(CharOperation.replace(this.source.toCharArray(), markerStart.toCharArray(), CharOperation.NO_CHAR));
			this.astEnd = this.source.indexOf(markerEnd); // end of AST exclusive
			this.source = new String(CharOperation.replace(this.source.toCharArray(), markerEnd.toCharArray(), CharOperation.NO_CHAR));	
		}
	}
	
	protected ASTNode findNode(CompilationUnit unit, final MarkerInfo markerInfo) {
		class EndVisit extends RuntimeException {
			private static final long serialVersionUID = 1L;
		}
		class Visitor extends ASTVisitor {
			ASTNode found;
			public void preVisit(ASTNode node) {
				if (node instanceof CompilationUnit) return;
				if (node.getStartPosition() == markerInfo.astStart && node.getStartPosition() + node.getLength() == markerInfo.astEnd) {
					this.found = node;
					throw new EndVisit();
				}
			}
		}
		Visitor visitor = new Visitor();
		try {
			unit.accept(visitor);
		} catch (EndVisit e) {
			return visitor.found;
		}
		return null;
	}

}
