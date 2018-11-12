/*******************************************************************************
 * Copyright (c) 2000, 2011 IBM Corporation and others.
 *
 * This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License 2.0
 * which accompanies this distribution, and is available at
 * https://www.eclipse.org/legal/epl-2.0/
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.jdt.internal.compiler.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.classfmt.ClassFileConstants;
import org.eclipse.jdt.internal.compiler.codegen.BranchLabel;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.impl.Constant;
import org.eclipse.jdt.internal.compiler.impl.IntConstant;
import org.eclipse.jdt.internal.compiler.lookup.Binding;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class CaseStatement extends Statement {

	public Expression constantExpression;
	public BranchLabel targetLabel;
	public Expression[] constantExpressions; // case with multiple expressions
	public boolean isExpr = false;

public CaseStatement(Expression constantExpression, int sourceEnd, int sourceStart) {
	this.constantExpression = constantExpression;
	this.sourceEnd = sourceEnd;
	this.sourceStart = sourceStart;
}

@Override
public FlowInfo analyseCode(
	BlockScope currentScope,
	FlowContext flowContext,
	FlowInfo flowInfo) {

	if (this.constantExpression != null) {
		if (this.constantExpression.constant == Constant.NotAConstant
				&& !this.constantExpression.resolvedType.isEnum()) {
			currentScope.problemReporter().caseExpressionMustBeConstant(this.constantExpression);
		}
		this.constantExpression.analyseCode(currentScope, flowContext, flowInfo);
	}
	return flowInfo;
}

@Override
public StringBuffer printStatement(int tab, StringBuffer output) {
	printIndent(tab, output);
	if (this.constantExpression == null) {
		output.append("default "); //$NON-NLS-1$
		output.append(this.isExpr ? "->" : ":"); //$NON-NLS-1$ //$NON-NLS-2$
	} else {
		output.append("case "); //$NON-NLS-1$
		if (this.constantExpressions != null && this.constantExpressions.length > 0) {
			for (int i = 0, l = this.constantExpressions.length; i < l; ++i) {
				this.constantExpressions[i].printExpression(0, output);
				if (i < l -1) output.append(',');
			}
		} else {
			this.constantExpression.printExpression(0, output);
		}
		output.append(this.isExpr ? " ->" : " :"); //$NON-NLS-1$ //$NON-NLS-2$
	}
	return output;
}

/**
 * Case code generation
 *
 */
@Override
public void generateCode(BlockScope currentScope, CodeStream codeStream) {
	if ((this.bits & ASTNode.IsReachable) == 0) {
		return;
	}
	int pc = codeStream.position;
	this.targetLabel.place();
	codeStream.recordPositionsFrom(pc, this.sourceStart);
}

/**
 * No-op : should use resolveCase(...) instead.
 */
@Override
public void resolve(BlockScope scope) {
	// no-op : should use resolveCase(...) instead.
}

/**
 * Returns the constant intValue or ordinal for enum constants. If constant is NotAConstant, then answers Float.MIN_VALUE
 * see org.eclipse.jdt.internal.compiler.ast.Statement#resolveCase(org.eclipse.jdt.internal.compiler.lookup.BlockScope, org.eclipse.jdt.internal.compiler.lookup.TypeBinding, org.eclipse.jdt.internal.compiler.ast.SwitchStatement)
 */
public Constant _resolveCase(BlockScope scope, TypeBinding switchExpressionType, SwitchStatement switchStatement) {
	// switchExpressionType maybe null in error case
	scope.enclosingCase = this; // record entering in a switch case block

	if (this.constantExpression == null) {
		// remember the default case into the associated switch statement
		if (switchStatement.defaultCase != null)
			scope.problemReporter().duplicateDefaultCase(this);

		// on error the last default will be the selected one ...
		switchStatement.defaultCase = this;
		return Constant.NotAConstant;
	}
	// add into the collection of cases of the associated switch statement
	switchStatement.cases[switchStatement.caseCount++] = this;
	// tag constant name with enum type for privileged access to its members
	if (switchExpressionType != null && switchExpressionType.isEnum() && (this.constantExpression instanceof SingleNameReference)) {
		((SingleNameReference) this.constantExpression).setActualReceiverType((ReferenceBinding)switchExpressionType);
	}
	TypeBinding caseType = this.constantExpression.resolveType(scope);
	if (caseType == null || switchExpressionType == null) return Constant.NotAConstant;
	if (this.constantExpression.isConstantValueOfTypeAssignableToType(caseType, switchExpressionType)
			|| caseType.isCompatibleWith(switchExpressionType)) {
		if (caseType.isEnum()) {
			if (((this.constantExpression.bits & ASTNode.ParenthesizedMASK) >> ASTNode.ParenthesizedSHIFT) != 0) {
				scope.problemReporter().enumConstantsCannotBeSurroundedByParenthesis(this.constantExpression);
			}

			if (this.constantExpression instanceof NameReference
					&& (this.constantExpression.bits & ASTNode.RestrictiveFlagMASK) == Binding.FIELD) {
				NameReference reference = (NameReference) this.constantExpression;
				FieldBinding field = reference.fieldBinding();
				if ((field.modifiers & ClassFileConstants.AccEnum) == 0) {
					 scope.problemReporter().enumSwitchCannotTargetField(reference, field);
				} else 	if (reference instanceof QualifiedNameReference) {
					 scope.problemReporter().cannotUseQualifiedEnumConstantInCaseLabel(reference, field);
				}
				return IntConstant.fromValue(field.original().id + 1); // (ordinal value + 1) zero should not be returned see bug 141810
			}
		} else {
			return this.constantExpression.constant;
		}
	} else if (isBoxingCompatible(caseType, switchExpressionType, this.constantExpression, scope)) {
		// constantExpression.computeConversion(scope, caseType, switchExpressionType); - do not report boxing/unboxing conversion
		return this.constantExpression.constant;
	}
	scope.problemReporter().typeMismatchError(caseType, switchExpressionType, this.constantExpression, switchStatement.expression);
	return Constant.NotAConstant;
}

/**
 * Returns the constant intValue or ordinal for enum constants. If constant is NotAConstant, then answers Float.MIN_VALUE
 * Switch Expressions in JLS 12 onwards
 */
@Override
public Constant resolveCase(BlockScope scope, TypeBinding switchExpressionExpressionType, Statement node) {
	boolean isSwitchStatement = node instanceof SwitchStatement;
	// switchExpressionType maybe null in error case
	scope.enclosingCase = this; // record entering in a switch case block

	if (this.constantExpression == null) {
		// remember the default case into the associated switch statement
		if (isSwitchStatement)
			setDefaultCase(scope, (SwitchStatement) node);
		else
			setDefaultCase(scope, (SwitchExpression) node);
		return Constant.NotAConstant;
	}
	// add into the collection of cases of the associated switch statement
	if (isSwitchStatement)
		addNormalCase((SwitchStatement) node);
	else
		addNormalCase((SwitchExpression) node);
	// tag constant name with enum type for privileged access to its members
	if (switchExpressionExpressionType != null && switchExpressionExpressionType.isEnum() && (this.constantExpression instanceof SingleNameReference)) {
		((SingleNameReference) this.constantExpression).setActualReceiverType((ReferenceBinding)switchExpressionExpressionType);
	}
	TypeBinding caseType = this.constantExpression.resolveType(scope);
	if (caseType == null || switchExpressionExpressionType == null) return Constant.NotAConstant;
	if (this.constantExpression.isConstantValueOfTypeAssignableToType(caseType, switchExpressionExpressionType)
			|| caseType.isCompatibleWith(switchExpressionExpressionType)) {
		if (caseType.isEnum()) {
			if (((this.constantExpression.bits & ASTNode.ParenthesizedMASK) >> ASTNode.ParenthesizedSHIFT) != 0) {
				scope.problemReporter().enumConstantsCannotBeSurroundedByParenthesis(this.constantExpression);
			}

			if (this.constantExpression instanceof NameReference
					&& (this.constantExpression.bits & ASTNode.RestrictiveFlagMASK) == Binding.FIELD) {
				NameReference reference = (NameReference) this.constantExpression;
				FieldBinding field = reference.fieldBinding();
				if ((field.modifiers & ClassFileConstants.AccEnum) == 0) {
					 scope.problemReporter().enumSwitchCannotTargetField(reference, field);
				} else 	if (reference instanceof QualifiedNameReference) {
					 scope.problemReporter().cannotUseQualifiedEnumConstantInCaseLabel(reference, field);
				}
				return IntConstant.fromValue(field.original().id + 1); // (ordinal value + 1) zero should not be returned see bug 141810
			}
		} else {
			return this.constantExpression.constant;
		}
	} else if (isBoxingCompatible(caseType, switchExpressionExpressionType, this.constantExpression, scope)) {
		// constantExpression.computeConversion(scope, caseType, switchExpressionType); - do not report boxing/unboxing conversion
		return this.constantExpression.constant;
	}
	Expression expression = isSwitchStatement ? ((SwitchStatement) node).expression : ((SwitchExpression) node).expression;
	scope.problemReporter().typeMismatchError(caseType, switchExpressionExpressionType, this.constantExpression, expression);
	return Constant.NotAConstant;
}

private void addNormalCase(SwitchStatement switchStatement) {
	switchStatement.cases[switchStatement.caseCount++] = this;
}

private void setDefaultCase(BlockScope scope, SwitchStatement switchStatement) {
	if (switchStatement.defaultCase != null)
		scope.problemReporter().duplicateDefaultCase(this);

	// on error the last default will be the selected one ...
	switchStatement.defaultCase = this;
}
private void addNormalCase(SwitchExpression switchExpression) {
	switchExpression.cases[switchExpression.caseCount++] = this;
}

private void setDefaultCase(BlockScope scope, SwitchExpression switchExpression) {
	if (switchExpression.defaultCase != null)
		scope.problemReporter().duplicateDefaultCase(this);

	// on error the last default will be the selected one ...
	switchExpression.defaultCase = this;
}

@Override
public void traverse(ASTVisitor visitor, 	BlockScope blockScope) {
	if (visitor.visit(this, blockScope)) {
		if (this.constantExpression != null) this.constantExpression.traverse(visitor, blockScope);
	}
	visitor.endVisit(this, blockScope);
}
}
