// Generated from /home/levente/Documents/University/theta-refactor/subprojects/frontends/litmus2xcfa/src/main/antlr/LitmusAssertions.g4 by ANTLR 4.9.3
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class LitmusAssertionsParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.9.3", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		AssertionListExpectationTest=1, AssertionAnd=2, AssertionOr=3, AssertionExists=4, 
		AssertionFinal=5, AssertionForall=6, AssertionFilter=7, AssertionNot=8, 
		AssertionWith=9, ThreadIdentifier=10, EqualsEquals=11, NotEquals=12, LessEquals=13, 
		GreaterEquals=14, Identifier=15, DigitSequence=16, Whitespace=17, Newline=18, 
		BlockComment=19, ExecConfig=20, Excl=21, Quot=22, Num=23, Dollar=24, Percent=25, 
		Amp=26, Apos=27, LPar=28, RPar=29, Ast=30, Plus=31, Comma=32, Minus=33, 
		Period=34, Slash=35, Colon=36, Semi=37, Less=38, Equals=39, Greater=40, 
		Question=41, At=42, LBracket=43, RBracket=44, BSlash=45, LBrace=46, RBrace=47, 
		Circ=48, Tilde=49, Bar=50, Underscore=51;
	public static final int
		RULE_assertionFilter = 0, RULE_assertionList = 1, RULE_assertion = 2, 
		RULE_assertionValue = 3, RULE_varName = 4, RULE_constant = 5, RULE_assertionListExpectationList = 6, 
		RULE_assertionListExpectation = 7, RULE_assertionCompare = 8, RULE_threadId = 9;
	private static String[] makeRuleNames() {
		return new String[] {
			"assertionFilter", "assertionList", "assertion", "assertionValue", "varName", 
			"constant", "assertionListExpectationList", "assertionListExpectation", 
			"assertionCompare", "threadId"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, null, "'/\\'", "'\\/'", "'exists'", "'final'", "'forall'", "'filter'", 
			null, "'with'", null, "'=='", "'!='", "'<='", "'>='", null, null, null, 
			null, null, null, "'!'", "'\"'", "'#'", "'$'", "'%'", "'&'", "'''", "'('", 
			"')'", "'*'", "'+'", "','", "'-'", "'.'", "'/'", "':'", "';'", "'<'", 
			"'='", "'>'", "'?'", "'@'", "'['", "']'", "'\\'", "'{'", "'}'", "'^'", 
			"'~'", "'|'", "'_'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "AssertionListExpectationTest", "AssertionAnd", "AssertionOr", 
			"AssertionExists", "AssertionFinal", "AssertionForall", "AssertionFilter", 
			"AssertionNot", "AssertionWith", "ThreadIdentifier", "EqualsEquals", 
			"NotEquals", "LessEquals", "GreaterEquals", "Identifier", "DigitSequence", 
			"Whitespace", "Newline", "BlockComment", "ExecConfig", "Excl", "Quot", 
			"Num", "Dollar", "Percent", "Amp", "Apos", "LPar", "RPar", "Ast", "Plus", 
			"Comma", "Minus", "Period", "Slash", "Colon", "Semi", "Less", "Equals", 
			"Greater", "Question", "At", "LBracket", "RBracket", "BSlash", "LBrace", 
			"RBrace", "Circ", "Tilde", "Bar", "Underscore"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "LitmusAssertions.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public LitmusAssertionsParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	public static class AssertionFilterContext extends ParserRuleContext {
		public AssertionContext a;
		public TerminalNode AssertionFilter() { return getToken(LitmusAssertionsParser.AssertionFilter, 0); }
		public AssertionContext assertion() {
			return getRuleContext(AssertionContext.class,0);
		}
		public TerminalNode Semi() { return getToken(LitmusAssertionsParser.Semi, 0); }
		public AssertionFilterContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertionFilter; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionFilter(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionFilter(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionFilter(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssertionFilterContext assertionFilter() throws RecognitionException {
		AssertionFilterContext _localctx = new AssertionFilterContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_assertionFilter);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(20);
			match(AssertionFilter);
			setState(21);
			((AssertionFilterContext)_localctx).a = assertion(0);
			setState(23);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==Semi) {
				{
				setState(22);
				match(Semi);
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssertionListContext extends ParserRuleContext {
		public AssertionContext a;
		public TerminalNode AssertionExists() { return getToken(LitmusAssertionsParser.AssertionExists, 0); }
		public AssertionContext assertion() {
			return getRuleContext(AssertionContext.class,0);
		}
		public TerminalNode Semi() { return getToken(LitmusAssertionsParser.Semi, 0); }
		public TerminalNode AssertionNot() { return getToken(LitmusAssertionsParser.AssertionNot, 0); }
		public TerminalNode AssertionForall() { return getToken(LitmusAssertionsParser.AssertionForall, 0); }
		public TerminalNode AssertionFinal() { return getToken(LitmusAssertionsParser.AssertionFinal, 0); }
		public AssertionListExpectationListContext assertionListExpectationList() {
			return getRuleContext(AssertionListExpectationListContext.class,0);
		}
		public AssertionListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertionList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssertionListContext assertionList() throws RecognitionException {
		AssertionListContext _localctx = new AssertionListContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_assertionList);
		int _la;
		try {
			setState(48);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case AssertionExists:
				enterOuterAlt(_localctx, 1);
				{
				setState(25);
				match(AssertionExists);
				setState(26);
				((AssertionListContext)_localctx).a = assertion(0);
				setState(28);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==Semi) {
					{
					setState(27);
					match(Semi);
					}
				}

				}
				break;
			case AssertionNot:
				enterOuterAlt(_localctx, 2);
				{
				setState(30);
				match(AssertionNot);
				setState(31);
				match(AssertionExists);
				setState(32);
				((AssertionListContext)_localctx).a = assertion(0);
				setState(34);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==Semi) {
					{
					setState(33);
					match(Semi);
					}
				}

				}
				break;
			case AssertionForall:
				enterOuterAlt(_localctx, 3);
				{
				setState(36);
				match(AssertionForall);
				setState(37);
				((AssertionListContext)_localctx).a = assertion(0);
				setState(39);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==Semi) {
					{
					setState(38);
					match(Semi);
					}
				}

				}
				break;
			case AssertionFinal:
				enterOuterAlt(_localctx, 4);
				{
				setState(41);
				match(AssertionFinal);
				setState(42);
				((AssertionListContext)_localctx).a = assertion(0);
				setState(44);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==Semi) {
					{
					setState(43);
					match(Semi);
					}
				}

				setState(46);
				assertionListExpectationList();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssertionContext extends ParserRuleContext {
		public AssertionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertion; }
	 
		public AssertionContext() { }
		public void copyFrom(AssertionContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class AssertionBasicContext extends AssertionContext {
		public List<AssertionValueContext> assertionValue() {
			return getRuleContexts(AssertionValueContext.class);
		}
		public AssertionValueContext assertionValue(int i) {
			return getRuleContext(AssertionValueContext.class,i);
		}
		public AssertionCompareContext assertionCompare() {
			return getRuleContext(AssertionCompareContext.class,0);
		}
		public AssertionBasicContext(AssertionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionBasic(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionBasic(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionBasic(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class AssertionAndContext extends AssertionContext {
		public List<AssertionContext> assertion() {
			return getRuleContexts(AssertionContext.class);
		}
		public AssertionContext assertion(int i) {
			return getRuleContext(AssertionContext.class,i);
		}
		public TerminalNode AssertionAnd() { return getToken(LitmusAssertionsParser.AssertionAnd, 0); }
		public AssertionAndContext(AssertionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionAnd(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionAnd(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionAnd(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class AssertionOrContext extends AssertionContext {
		public List<AssertionContext> assertion() {
			return getRuleContexts(AssertionContext.class);
		}
		public AssertionContext assertion(int i) {
			return getRuleContext(AssertionContext.class,i);
		}
		public TerminalNode AssertionOr() { return getToken(LitmusAssertionsParser.AssertionOr, 0); }
		public AssertionOrContext(AssertionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionOr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionOr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionOr(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class AssertionParenthesisContext extends AssertionContext {
		public TerminalNode LPar() { return getToken(LitmusAssertionsParser.LPar, 0); }
		public AssertionContext assertion() {
			return getRuleContext(AssertionContext.class,0);
		}
		public TerminalNode RPar() { return getToken(LitmusAssertionsParser.RPar, 0); }
		public AssertionParenthesisContext(AssertionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionParenthesis(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionParenthesis(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionParenthesis(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class AssertionNotContext extends AssertionContext {
		public TerminalNode AssertionNot() { return getToken(LitmusAssertionsParser.AssertionNot, 0); }
		public AssertionContext assertion() {
			return getRuleContext(AssertionContext.class,0);
		}
		public AssertionNotContext(AssertionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionNot(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionNot(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionNot(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssertionContext assertion() throws RecognitionException {
		return assertion(0);
	}

	private AssertionContext assertion(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		AssertionContext _localctx = new AssertionContext(_ctx, _parentState);
		AssertionContext _prevctx = _localctx;
		int _startState = 4;
		enterRecursionRule(_localctx, 4, RULE_assertion, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(61);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case LPar:
				{
				_localctx = new AssertionParenthesisContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;

				setState(51);
				match(LPar);
				setState(52);
				assertion(0);
				setState(53);
				match(RPar);
				}
				break;
			case AssertionNot:
				{
				_localctx = new AssertionNotContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(55);
				match(AssertionNot);
				setState(56);
				assertion(4);
				}
				break;
			case ThreadIdentifier:
			case Identifier:
			case DigitSequence:
			case Minus:
			case Underscore:
				{
				_localctx = new AssertionBasicContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(57);
				assertionValue();
				setState(58);
				assertionCompare();
				setState(59);
				assertionValue();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			_ctx.stop = _input.LT(-1);
			setState(71);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,8,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(69);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,7,_ctx) ) {
					case 1:
						{
						_localctx = new AssertionAndContext(new AssertionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_assertion);
						setState(63);
						if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
						setState(64);
						match(AssertionAnd);
						setState(65);
						assertion(4);
						}
						break;
					case 2:
						{
						_localctx = new AssertionOrContext(new AssertionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_assertion);
						setState(66);
						if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
						setState(67);
						match(AssertionOr);
						setState(68);
						assertion(3);
						}
						break;
					}
					} 
				}
				setState(73);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,8,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class AssertionValueContext extends ParserRuleContext {
		public VarNameContext varName() {
			return getRuleContext(VarNameContext.class,0);
		}
		public TerminalNode LBracket() { return getToken(LitmusAssertionsParser.LBracket, 0); }
		public TerminalNode DigitSequence() { return getToken(LitmusAssertionsParser.DigitSequence, 0); }
		public TerminalNode RBracket() { return getToken(LitmusAssertionsParser.RBracket, 0); }
		public ThreadIdContext threadId() {
			return getRuleContext(ThreadIdContext.class,0);
		}
		public TerminalNode Colon() { return getToken(LitmusAssertionsParser.Colon, 0); }
		public ConstantContext constant() {
			return getRuleContext(ConstantContext.class,0);
		}
		public AssertionValueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertionValue; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionValue(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionValue(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionValue(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssertionValueContext assertionValue() throws RecognitionException {
		AssertionValueContext _localctx = new AssertionValueContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_assertionValue);
		try {
			setState(85);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,9,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(74);
				varName();
				setState(75);
				match(LBracket);
				setState(76);
				match(DigitSequence);
				setState(77);
				match(RBracket);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(79);
				varName();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(80);
				threadId();
				setState(81);
				match(Colon);
				setState(82);
				varName();
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(84);
				constant();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VarNameContext extends ParserRuleContext {
		public List<TerminalNode> Identifier() { return getTokens(LitmusAssertionsParser.Identifier); }
		public TerminalNode Identifier(int i) {
			return getToken(LitmusAssertionsParser.Identifier, i);
		}
		public List<TerminalNode> Underscore() { return getTokens(LitmusAssertionsParser.Underscore); }
		public TerminalNode Underscore(int i) {
			return getToken(LitmusAssertionsParser.Underscore, i);
		}
		public List<TerminalNode> DigitSequence() { return getTokens(LitmusAssertionsParser.DigitSequence); }
		public TerminalNode DigitSequence(int i) {
			return getToken(LitmusAssertionsParser.DigitSequence, i);
		}
		public VarNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varName; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterVarName(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitVarName(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitVarName(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VarNameContext varName() throws RecognitionException {
		VarNameContext _localctx = new VarNameContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_varName);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(90);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==Underscore) {
				{
				{
				setState(87);
				match(Underscore);
				}
				}
				setState(92);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(93);
			match(Identifier);
			setState(97);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,11,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					{
					{
					setState(94);
					_la = _input.LA(1);
					if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << Identifier) | (1L << DigitSequence) | (1L << Underscore))) != 0)) ) {
					_errHandler.recoverInline(this);
					}
					else {
						if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
						_errHandler.reportMatch(this);
						consume();
					}
					}
					} 
				}
				setState(99);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,11,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ConstantContext extends ParserRuleContext {
		public TerminalNode DigitSequence() { return getToken(LitmusAssertionsParser.DigitSequence, 0); }
		public TerminalNode Minus() { return getToken(LitmusAssertionsParser.Minus, 0); }
		public ConstantContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_constant; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterConstant(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitConstant(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitConstant(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ConstantContext constant() throws RecognitionException {
		ConstantContext _localctx = new ConstantContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_constant);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(101);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==Minus) {
				{
				setState(100);
				match(Minus);
				}
			}

			setState(103);
			match(DigitSequence);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssertionListExpectationListContext extends ParserRuleContext {
		public TerminalNode AssertionWith() { return getToken(LitmusAssertionsParser.AssertionWith, 0); }
		public List<AssertionListExpectationContext> assertionListExpectation() {
			return getRuleContexts(AssertionListExpectationContext.class);
		}
		public AssertionListExpectationContext assertionListExpectation(int i) {
			return getRuleContext(AssertionListExpectationContext.class,i);
		}
		public AssertionListExpectationListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertionListExpectationList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionListExpectationList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionListExpectationList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionListExpectationList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssertionListExpectationListContext assertionListExpectationList() throws RecognitionException {
		AssertionListExpectationListContext _localctx = new AssertionListExpectationListContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_assertionListExpectationList);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(105);
			match(AssertionWith);
			setState(107); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(106);
				assertionListExpectation();
				}
				}
				setState(109); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( _la==AssertionListExpectationTest );
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssertionListExpectationContext extends ParserRuleContext {
		public TerminalNode AssertionListExpectationTest() { return getToken(LitmusAssertionsParser.AssertionListExpectationTest, 0); }
		public TerminalNode Colon() { return getToken(LitmusAssertionsParser.Colon, 0); }
		public TerminalNode AssertionExists() { return getToken(LitmusAssertionsParser.AssertionExists, 0); }
		public TerminalNode Semi() { return getToken(LitmusAssertionsParser.Semi, 0); }
		public TerminalNode AssertionNot() { return getToken(LitmusAssertionsParser.AssertionNot, 0); }
		public AssertionListExpectationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertionListExpectation; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterAssertionListExpectation(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitAssertionListExpectation(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitAssertionListExpectation(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssertionListExpectationContext assertionListExpectation() throws RecognitionException {
		AssertionListExpectationContext _localctx = new AssertionListExpectationContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_assertionListExpectation);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(111);
			match(AssertionListExpectationTest);
			setState(112);
			match(Colon);
			setState(114);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==AssertionNot) {
				{
				setState(113);
				match(AssertionNot);
				}
			}

			setState(116);
			match(AssertionExists);
			setState(117);
			match(Semi);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssertionCompareContext extends ParserRuleContext {
		public AssertionCompareContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assertionCompare; }
	 
		public AssertionCompareContext() { }
		public void copyFrom(AssertionCompareContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class GeqCompareContext extends AssertionCompareContext {
		public TerminalNode GreaterEquals() { return getToken(LitmusAssertionsParser.GreaterEquals, 0); }
		public GeqCompareContext(AssertionCompareContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterGeqCompare(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitGeqCompare(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitGeqCompare(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class NeqCompareContext extends AssertionCompareContext {
		public TerminalNode NotEquals() { return getToken(LitmusAssertionsParser.NotEquals, 0); }
		public NeqCompareContext(AssertionCompareContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterNeqCompare(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitNeqCompare(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitNeqCompare(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class GtCompareContext extends AssertionCompareContext {
		public TerminalNode Greater() { return getToken(LitmusAssertionsParser.Greater, 0); }
		public GtCompareContext(AssertionCompareContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterGtCompare(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitGtCompare(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitGtCompare(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class LtCompareContext extends AssertionCompareContext {
		public TerminalNode Less() { return getToken(LitmusAssertionsParser.Less, 0); }
		public LtCompareContext(AssertionCompareContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterLtCompare(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitLtCompare(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitLtCompare(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class EqCompareContext extends AssertionCompareContext {
		public TerminalNode Equals() { return getToken(LitmusAssertionsParser.Equals, 0); }
		public TerminalNode EqualsEquals() { return getToken(LitmusAssertionsParser.EqualsEquals, 0); }
		public EqCompareContext(AssertionCompareContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterEqCompare(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitEqCompare(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitEqCompare(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class LeqCompareContext extends AssertionCompareContext {
		public TerminalNode LessEquals() { return getToken(LitmusAssertionsParser.LessEquals, 0); }
		public LeqCompareContext(AssertionCompareContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterLeqCompare(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitLeqCompare(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitLeqCompare(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssertionCompareContext assertionCompare() throws RecognitionException {
		AssertionCompareContext _localctx = new AssertionCompareContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_assertionCompare);
		int _la;
		try {
			setState(125);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case EqualsEquals:
			case Equals:
				_localctx = new EqCompareContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(119);
				_la = _input.LA(1);
				if ( !(_la==EqualsEquals || _la==Equals) ) {
				_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				}
				break;
			case NotEquals:
				_localctx = new NeqCompareContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(120);
				match(NotEquals);
				}
				break;
			case GreaterEquals:
				_localctx = new GeqCompareContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(121);
				match(GreaterEquals);
				}
				break;
			case LessEquals:
				_localctx = new LeqCompareContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(122);
				match(LessEquals);
				}
				break;
			case Less:
				_localctx = new LtCompareContext(_localctx);
				enterOuterAlt(_localctx, 5);
				{
				setState(123);
				match(Less);
				}
				break;
			case Greater:
				_localctx = new GtCompareContext(_localctx);
				enterOuterAlt(_localctx, 6);
				{
				setState(124);
				match(Greater);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ThreadIdContext extends ParserRuleContext {
		public int id;
		public Token t;
		public TerminalNode ThreadIdentifier() { return getToken(LitmusAssertionsParser.ThreadIdentifier, 0); }
		public TerminalNode DigitSequence() { return getToken(LitmusAssertionsParser.DigitSequence, 0); }
		public ThreadIdContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_threadId; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).enterThreadId(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof LitmusAssertionsListener ) ((LitmusAssertionsListener)listener).exitThreadId(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LitmusAssertionsVisitor ) return ((LitmusAssertionsVisitor<? extends T>)visitor).visitThreadId(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ThreadIdContext threadId() throws RecognitionException {
		ThreadIdContext _localctx = new ThreadIdContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_threadId);
		try {
			setState(131);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case ThreadIdentifier:
				enterOuterAlt(_localctx, 1);
				{
				setState(127);
				((ThreadIdContext)_localctx).t = match(ThreadIdentifier);
				((ThreadIdContext)_localctx).id =  Integer.parseInt((((ThreadIdContext)_localctx).t!=null?((ThreadIdContext)_localctx).t.getText():null).replace("P", ""));
				}
				break;
			case DigitSequence:
				enterOuterAlt(_localctx, 2);
				{
				setState(129);
				((ThreadIdContext)_localctx).t = match(DigitSequence);
				((ThreadIdContext)_localctx).id =  Integer.parseInt((((ThreadIdContext)_localctx).t!=null?((ThreadIdContext)_localctx).t.getText():null));
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 2:
			return assertion_sempred((AssertionContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean assertion_sempred(AssertionContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 3);
		case 1:
			return precpred(_ctx, 2);
		}
		return true;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\65\u0088\4\2\t\2"+
		"\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\3\2\3\2\3\2\5\2\32\n\2\3\3\3\3\3\3\5\3\37\n\3\3\3\3\3\3\3\3\3\5"+
		"\3%\n\3\3\3\3\3\3\3\5\3*\n\3\3\3\3\3\3\3\5\3/\n\3\3\3\3\3\5\3\63\n\3\3"+
		"\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\5\4@\n\4\3\4\3\4\3\4\3\4\3"+
		"\4\3\4\7\4H\n\4\f\4\16\4K\13\4\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5"+
		"\3\5\5\5X\n\5\3\6\7\6[\n\6\f\6\16\6^\13\6\3\6\3\6\7\6b\n\6\f\6\16\6e\13"+
		"\6\3\7\5\7h\n\7\3\7\3\7\3\b\3\b\6\bn\n\b\r\b\16\bo\3\t\3\t\3\t\5\tu\n"+
		"\t\3\t\3\t\3\t\3\n\3\n\3\n\3\n\3\n\3\n\5\n\u0080\n\n\3\13\3\13\3\13\3"+
		"\13\5\13\u0086\n\13\3\13\2\3\6\f\2\4\6\b\n\f\16\20\22\24\2\4\4\2\21\22"+
		"\65\65\4\2\r\r))\2\u0097\2\26\3\2\2\2\4\62\3\2\2\2\6?\3\2\2\2\bW\3\2\2"+
		"\2\n\\\3\2\2\2\fg\3\2\2\2\16k\3\2\2\2\20q\3\2\2\2\22\177\3\2\2\2\24\u0085"+
		"\3\2\2\2\26\27\7\t\2\2\27\31\5\6\4\2\30\32\7\'\2\2\31\30\3\2\2\2\31\32"+
		"\3\2\2\2\32\3\3\2\2\2\33\34\7\6\2\2\34\36\5\6\4\2\35\37\7\'\2\2\36\35"+
		"\3\2\2\2\36\37\3\2\2\2\37\63\3\2\2\2 !\7\n\2\2!\"\7\6\2\2\"$\5\6\4\2#"+
		"%\7\'\2\2$#\3\2\2\2$%\3\2\2\2%\63\3\2\2\2&\'\7\b\2\2\')\5\6\4\2(*\7\'"+
		"\2\2)(\3\2\2\2)*\3\2\2\2*\63\3\2\2\2+,\7\7\2\2,.\5\6\4\2-/\7\'\2\2.-\3"+
		"\2\2\2./\3\2\2\2/\60\3\2\2\2\60\61\5\16\b\2\61\63\3\2\2\2\62\33\3\2\2"+
		"\2\62 \3\2\2\2\62&\3\2\2\2\62+\3\2\2\2\63\5\3\2\2\2\64\65\b\4\1\2\65\66"+
		"\7\36\2\2\66\67\5\6\4\2\678\7\37\2\28@\3\2\2\29:\7\n\2\2:@\5\6\4\6;<\5"+
		"\b\5\2<=\5\22\n\2=>\5\b\5\2>@\3\2\2\2?\64\3\2\2\2?9\3\2\2\2?;\3\2\2\2"+
		"@I\3\2\2\2AB\f\5\2\2BC\7\4\2\2CH\5\6\4\6DE\f\4\2\2EF\7\5\2\2FH\5\6\4\5"+
		"GA\3\2\2\2GD\3\2\2\2HK\3\2\2\2IG\3\2\2\2IJ\3\2\2\2J\7\3\2\2\2KI\3\2\2"+
		"\2LM\5\n\6\2MN\7-\2\2NO\7\22\2\2OP\7.\2\2PX\3\2\2\2QX\5\n\6\2RS\5\24\13"+
		"\2ST\7&\2\2TU\5\n\6\2UX\3\2\2\2VX\5\f\7\2WL\3\2\2\2WQ\3\2\2\2WR\3\2\2"+
		"\2WV\3\2\2\2X\t\3\2\2\2Y[\7\65\2\2ZY\3\2\2\2[^\3\2\2\2\\Z\3\2\2\2\\]\3"+
		"\2\2\2]_\3\2\2\2^\\\3\2\2\2_c\7\21\2\2`b\t\2\2\2a`\3\2\2\2be\3\2\2\2c"+
		"a\3\2\2\2cd\3\2\2\2d\13\3\2\2\2ec\3\2\2\2fh\7#\2\2gf\3\2\2\2gh\3\2\2\2"+
		"hi\3\2\2\2ij\7\22\2\2j\r\3\2\2\2km\7\13\2\2ln\5\20\t\2ml\3\2\2\2no\3\2"+
		"\2\2om\3\2\2\2op\3\2\2\2p\17\3\2\2\2qr\7\3\2\2rt\7&\2\2su\7\n\2\2ts\3"+
		"\2\2\2tu\3\2\2\2uv\3\2\2\2vw\7\6\2\2wx\7\'\2\2x\21\3\2\2\2y\u0080\t\3"+
		"\2\2z\u0080\7\16\2\2{\u0080\7\20\2\2|\u0080\7\17\2\2}\u0080\7(\2\2~\u0080"+
		"\7*\2\2\177y\3\2\2\2\177z\3\2\2\2\177{\3\2\2\2\177|\3\2\2\2\177}\3\2\2"+
		"\2\177~\3\2\2\2\u0080\23\3\2\2\2\u0081\u0082\7\f\2\2\u0082\u0086\b\13"+
		"\1\2\u0083\u0084\7\22\2\2\u0084\u0086\b\13\1\2\u0085\u0081\3\2\2\2\u0085"+
		"\u0083\3\2\2\2\u0086\25\3\2\2\2\23\31\36$).\62?GIW\\cgot\177\u0085";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}