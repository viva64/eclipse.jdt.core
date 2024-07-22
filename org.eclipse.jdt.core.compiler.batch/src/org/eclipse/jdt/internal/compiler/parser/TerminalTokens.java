/*******************************************************************************
 * Copyright (c) 2000, 2022 IBM Corporation and others.
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
package org.eclipse.jdt.internal.compiler.parser;

/**
 * IMPORTANT NOTE: These constants are dedicated to the internal Scanner implementation.
 * It is mirrored in org.eclipse.jdt.core.compiler public package where it is API.
 * The mirror implementation is using the backward compatible ITerminalSymbols constant
 * definitions (stable with 2.0), whereas the internal implementation uses TerminalTokens
 * which constant values reflect the latest parser generation state.
 */
/**
 * Maps each terminal symbol in the java-grammar into a unique integer.
 * This integer is used to represent the terminal when computing a parsing action.
 *
 * Disclaimer : These constant values are generated automatically using a Java
 * grammar, therefore their actual values are subject to change if new keywords
 * were added to the language (for instance, 'assert' is a keyword in 1.4).
 */
public interface TerminalTokens {

	// special tokens not part of grammar - not autogenerated
	int TokenNameNotAToken = 0,
							TokenNameWHITESPACE = 1000,
							TokenNameCOMMENT_LINE = 1001,
							TokenNameCOMMENT_BLOCK = 1002,
							TokenNameCOMMENT_JAVADOC = 1003,
							TokenNameSingleQuoteStringLiteral = 1004;

	static boolean isRestrictedKeyword(int tokenType) {
        switch (tokenType) {
            case TokenNameRestrictedIdentifierYield:
            case TokenNameRestrictedIdentifierrecord:
            case TokenNameRestrictedIdentifierWhen:
            case TokenNameRestrictedIdentifiersealed:
            case TokenNameRestrictedIdentifierpermits:
                return true;
            default:
                return false;
		}
	}

	static int getRestrictedKeyword(char [] text) {
		if (text != null) {
			int len = text.length;
			if (len == 4 && text[0] == 'w' ||
				len == 5 && text[0] == 'y' ||
				len == 6 && (text[0] == 'r' || text[0] == 's') ||
				len == 7 && text[0] == 'p') {
				return getRestrictedKeyword(new String(text));
			}
		}
		return TokenNameNotAToken;
	}

	static int getRestrictedKeyword(String text) {
        switch (text) {
			case "yield"  : return TokenNameRestrictedIdentifierYield;   //$NON-NLS-1$
			case "record" : return TokenNameRestrictedIdentifierrecord;  //$NON-NLS-1$
			case "when"   : return TokenNameRestrictedIdentifierWhen;    //$NON-NLS-1$
			case "sealed" : return TokenNameRestrictedIdentifiersealed;  //$NON-NLS-1$
			case "permits": return TokenNameRestrictedIdentifierpermits; //$NON-NLS-1$
            default:        return TokenNameNotAToken;
		}
	}

	// BEGIN_AUTOGENERATED_REGION
	int TokenNameIdentifier = 22,
							TokenNameabstract = 42,
							TokenNameassert = 82,
							TokenNameboolean = 106,
							TokenNamebreak = 83,
							TokenNamebyte = 107,
							TokenNamecase = 92,
							TokenNamecatch = 108,
							TokenNamechar = 109,
							TokenNameclass = 71,
							TokenNamecontinue = 84,
							TokenNameconst = 138,
							TokenNamedefault = 77,
							TokenNamedo = 85,
							TokenNamedouble = 110,
							TokenNameelse = 124,
							TokenNameenum = 75,
							TokenNameextends = 93,
							TokenNamefalse = 55,
							TokenNamefinal = 43,
							TokenNamefinally = 117,
							TokenNamefloat = 111,
							TokenNamefor = 86,
							TokenNamegoto = 139,
							TokenNameif = 87,
							TokenNameimplements = 135,
							TokenNameimport = 112,
							TokenNameinstanceof = 16,
							TokenNameint = 113,
							TokenNameinterface = 74,
							TokenNamelong = 114,
							TokenNamenative = 44,
							TokenNamenew = 40,
							TokenNamenon_sealed = 45,
							TokenNamenull = 56,
							TokenNamepackage = 91,
							TokenNameprivate = 46,
							TokenNameprotected = 47,
							TokenNamepublic = 48,
							TokenNamereturn = 88,
							TokenNameshort = 115,
							TokenNamestatic = 36,
							TokenNamestrictfp = 49,
							TokenNamesuper = 37,
							TokenNameswitch = 65,
							TokenNamesynchronized = 39,
							TokenNamethis = 38,
							TokenNamethrow = 79,
							TokenNamethrows = 118,
							TokenNametransient = 50,
							TokenNametrue = 57,
							TokenNametry = 89,
							TokenNamevoid = 116,
							TokenNamevolatile = 51,
							TokenNamewhile = 80,
							TokenNamemodule = 119,
							TokenNameopen = 120,
							TokenNamerequires = 125,
							TokenNametransitive = 131,
							TokenNameexports = 126,
							TokenNameopens = 127,
							TokenNameto = 136,
							TokenNameuses = 128,
							TokenNameprovides = 129,
							TokenNamewith = 137,
							TokenNameIntegerLiteral = 58,
							TokenNameLongLiteral = 59,
							TokenNameFloatingPointLiteral = 60,
							TokenNameDoubleLiteral = 61,
							TokenNameCharacterLiteral = 62,
							TokenNameStringLiteral = 53,
							TokenNameTextBlock = 54,
							TokenNameStringTemplate = 121,
							TokenNameTextBlockTemplate = 122,
							TokenNamePLUS_PLUS = 2,
							TokenNameMINUS_MINUS = 3,
							TokenNameEQUAL_EQUAL = 19,
							TokenNameLESS_EQUAL = 12,
							TokenNameGREATER_EQUAL = 13,
							TokenNameNOT_EQUAL = 20,
							TokenNameLEFT_SHIFT = 18,
							TokenNameRIGHT_SHIFT = 14,
							TokenNameUNSIGNED_RIGHT_SHIFT = 17,
							TokenNamePLUS_EQUAL = 94,
							TokenNameMINUS_EQUAL = 95,
							TokenNameMULTIPLY_EQUAL = 96,
							TokenNameDIVIDE_EQUAL = 97,
							TokenNameAND_EQUAL = 98,
							TokenNameOR_EQUAL = 99,
							TokenNameXOR_EQUAL = 100,
							TokenNameREMAINDER_EQUAL = 101,
							TokenNameLEFT_SHIFT_EQUAL = 102,
							TokenNameRIGHT_SHIFT_EQUAL = 103,
							TokenNameUNSIGNED_RIGHT_SHIFT_EQUAL = 104,
							TokenNameOR_OR = 31,
							TokenNameAND_AND = 30,
							TokenNamePLUS = 4,
							TokenNameMINUS = 5,
							TokenNameNOT = 67,
							TokenNameREMAINDER = 9,
							TokenNameXOR = 23,
							TokenNameAND = 21,
							TokenNameMULTIPLY = 8,
							TokenNameOR = 27,
							TokenNameTWIDDLE = 68,
							TokenNameDIVIDE = 10,
							TokenNameGREATER = 15,
							TokenNameLESS = 11,
							TokenNameLPAREN = 24,
							TokenNameRPAREN = 25,
							TokenNameLBRACE = 52,
							TokenNameRBRACE = 33,
							TokenNameLBRACKET = 6,
							TokenNameRBRACKET = 69,
							TokenNameSEMICOLON = 26,
							TokenNameQUESTION = 29,
							TokenNameCOLON = 66,
							TokenNameCOMMA = 32,
							TokenNameDOT = 1,
							TokenNameEQUAL = 78,
							TokenNameAT = 35,
							TokenNameELLIPSIS = 123,
							TokenNameARROW = 105,
							TokenNameCOLON_COLON = 7,
							TokenNameBeginLambda = 63,
							TokenNameBeginIntersectionCast = 70,
							TokenNameBeginTypeArguments = 90,
							TokenNameElidedSemicolonAndRightBrace = 72,
							TokenNameAT308 = 28,
							TokenNameAT308DOTDOTDOT = 132,
							TokenNameBeginCaseExpr = 73,
							TokenNameRestrictedIdentifierYield = 81,
							TokenNameRestrictedIdentifierrecord = 76,
							TokenNameRestrictedIdentifiersealed = 41,
							TokenNameRestrictedIdentifierpermits = 130,
							TokenNameBeginCaseElement = 133,
							TokenNameRestrictedIdentifierWhen = 134,
							TokenNameUNDERSCORE = 34,
							TokenNameEOF = 64,
							TokenNameERROR = 140;
}
