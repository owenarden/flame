# Args to vtc are: extra compile flags

# def f( name, opts ):
#   opts.extra_hc_opts = '-fno-warn-incomplete-patterns'
#setTestOpts(f)

test('eqTSym', normal, compile, ['-fplugin Flame.Solver'])
test('eqTTrans', normal, compile, ['-fplugin Flame.Solver'])
test('eqTTrans2', normal, compile, ['-fplugin Flame.Solver'])
test('eqTTrans3', normal, compile, ['-fplugin Flame.Solver'])
test('eqTTrans4', normal, compile, ['-fplugin Flame.Solver'])
test('eqTConjComm', normal, compile, ['-fplugin Flame.Solver'])
test('eqTDisjComm', normal, compile, ['-fplugin Flame.Solver'])
test('eqTConjAssoc', normal, compile, ['-fplugin Flame.Solver'])
test('eqTDisjAssoc', normal, compile, ['-fplugin Flame.Solver'])
test('eqTDisjAbsorb', normal, compile, ['-fplugin Flame.Solver'])
test('eqTConjAbsorb', normal, compile, ['-fplugin Flame.Solver'])
test('eqTConjIdemp', normal, compile, ['-fplugin Flame.Solver'])
test('eqTDisjIdemp', normal, compile, ['-fplugin Flame.Solver'])
test('eqTConjIdent', normal, compile, ['-fplugin Flame.Solver'])
test('eqTDisjIdent', normal, compile, ['-fplugin Flame.Solver'])
test('eqTConjTop', normal, compile, ['-fplugin Flame.Solver'])
test('eqTDisjBot', normal, compile, ['-fplugin Flame.Solver'])
test('eqTConjDistDisj', normal, compile, ['-fplugin Flame.Solver'])
test('eqTConjConf', normal, compile, ['-fplugin Flame.Solver'])
test('eqTConjInteg', normal, compile, ['-fplugin Flame.Solver'])
test('eqTDisjConf', normal, compile, ['-fplugin Flame.Solver'])
test('eqTDisjInteg', normal, compile, ['-fplugin Flame.Solver'])
test('eqTConfIdemp', normal, compile, ['-fplugin Flame.Solver'])
test('eqTIntegIdemp', normal, compile, ['-fplugin Flame.Solver'])
test('eqTConfInteg', normal, compile, ['-fplugin Flame.Solver'])
test('eqTIntegConf', normal, compile, ['-fplugin Flame.Solver'])
test('eqTConfDisjInteg', normal, compile, ['-fplugin Flame.Solver'])
test('eqTConfIntegBasis', normal, compile, ['-fplugin Flame.Solver'])
test('eqTBotConf', normal, compile, ['-fplugin Flame.Solver'])
test('eqTBotInteg', normal, compile, ['-fplugin Flame.Solver'])
test('eqTNomEq', normal, compile, ['-fplugin Flame.Solver'])
test('infer001', normal, compile, ['-fplugin Flame.Solver'])
test('infer002', normal, compile, ['-fplugin Flame.Solver'])
test('join001', normal, compile, ['-fplugin Flame.Solver'])
