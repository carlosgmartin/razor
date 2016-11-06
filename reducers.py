from entities import *
from functools import lru_cache

@lru_cache(maxsize=None)
def lift(term, offset, depth=0):
	'''Increment indices of variables that are free at given depth'''
	assert isinstance(term, Term)
	assert isinstance(offset, int)
	if isinstance(term, Constant):
		return term
	if isinstance(term, Variable):
		if term.index < depth:
			# Bound variable
			return term
		else:
			# Free variable
			return Variable(term.index + offset)
	elif isinstance(term, Abstraction):
		return Abstraction(term.type, lift(term.body, offset, depth + 1))
	elif isinstance(term, Application):
		return Application(lift(term.function, offset, depth), lift(term.argument, offset, depth))

@lru_cache(maxsize=None)
def substitution(term, substitute, index=0):
	'''Substitute the variable with the specified index'''
	assert isinstance(term, Term)
	assert isinstance(substitute, Term)
	if isinstance(term, Constant):
		return term
	elif isinstance(term, Variable):
		if term.index < index:
			return term
		elif term.index == index:
			return lift(substitute, index)
		else:
			return Variable(term.index - 1)
	elif isinstance(term, Abstraction):
		return Abstraction(term.type, substitution(term.body, substitute, index + 1))
	elif isinstance(term, Application):
		return Application(substitution(term.function, substitute, index), substitution(term.argument, substitute, index))





# Beta reduction

@lru_cache(maxsize=None)
def is_beta_reducible(term):
	assert isinstance(term, Term)
	return isinstance(term, Application) and isinstance(term.function, Abstraction)

@lru_cache(maxsize=None)
def beta_reduce(term):
	assert isinstance(term, Term)
	return substitution(term.function.body, term.argument)




# Eta reduction
# Example: (λ:ℕ (succ 0)) → succ

@lru_cache(maxsize=None)
def occurs(variable, term):
	'''Returns whether a variable occurs in a term'''
	assert isinstance(variable, Variable)
	assert isinstance(term, Term)
	if isinstance(term, Constant):
		return False
	elif isinstance(term, Variable):
		return term.index == variable.index
	elif isinstance(term, Abstraction):
		return occurs(Variable(variable.index + 1), term.body)
	elif isinstance(term, Application):
		return occurs(variable, term.function) or occurs(variable, term.argument)

@lru_cache(maxsize=None)
def is_eta_reducible(term):
	assert isinstance(term, Term)
	return isinstance(term, Abstraction) and isinstance(term.body, Application) and term.body.argument == Variable(0) and not occurs(Variable(0), term.body.function)

@lru_cache(maxsize=None)
def eta_reduce(term):
	assert isinstance(term, Term)
	return lift(term.body.function, -1)



# Iteration reduction
# iter zero f x → x
# iter (succ i) f x → f (iter i f x)
# Example: (((iter zero) succ) zero) → zero

natural = BaseType('\u2115')

@lru_cache(maxsize=None)
def is_iter_reducible(term):
	assert isinstance(term, Term)

	# New version
	if isinstance(term, Application) and term.function == Constant('iter'):
		if term.argument == Constant('zero'):
			return True
		elif isinstance(term.argument, Application) and term.argument.function == Constant('succ'):
			return True
	return False

	# Old version
	return (
		isinstance(term, Application) and
		isinstance(term.function, Application) and
		isinstance(term.function.function, Application) and
		term.function.function.function == Constant('iter') and
		(
			term.function.function.argument == Constant('zero') or
			(
				isinstance(term.function.function.argument, Application) and
				term.function.function.argument.function == Constant('succ')
			)
		)
	)

@lru_cache(maxsize=None)
def iter_reduce(term):
	# New version
	if isinstance(term, Application) and term.function == Constant('iter'):
		if term.argument == Constant('zero'):
			return Abstraction(
				FunctionType(natural, natural),
				Abstraction(
					natural,
					Variable(0)
				)
			)
		elif isinstance(term.argument, Application) and term.argument.function == Constant('succ'):
			i = term.argument.argument
			return Abstraction(
				FunctionType(natural, natural),
				Abstraction(
					natural,
					Application(
						Variable(1),
						Application(
							Application(
								Application(
									Constant('iter'),
									lift(i, 2)
								),
								Variable(1)
							),
							Variable(0)
						)
					)
				)
			)

	raise Exception('Not iter reducible')

	# Old version
	x = term.argument
	if term.function.function.argument == Constant('zero'):
		return x
	else:
		f = term.function.argument
		i = term.function.function.argument.argument
		return Application(f, Application(Application(Application(Constant('iter'), i), f), x))





# Inductive reduction?

# f zero = g zero
# f n = g n ⇒ f (suc n) = g (suc n)
# ⊢ f = g

# ∃x s.t. f n ⇒ x, g n ⇒ x
# ⇒ ∃y s.t. f (suc n) ⇒ y, g (suc n) ⇒ y
# ⊢ f n = g n ⇒ f (suc n) = g (suc n)

# f n ↓ g n ⇒ f (suc n) ↓ g (suc n)
# ⊢ f n = g n ⇒ f (suc n) = g (suc n)






@lru_cache(maxsize=None)
def is_head_reducible(term):
	'''Returns whether a term is a redex'''
	return is_beta_reducible(term) or is_eta_reducible(term) or is_iter_reducible(term)

@lru_cache(maxsize=None)
def head_reduce(term):
	if is_beta_reducible(term):
		return beta_reduce(term)
	elif is_eta_reducible(term):
		return eta_reduce(term)
	elif is_iter_reducible(term):
		return iter_reduce(term)

@lru_cache(maxsize=None)
def head_normalize(term):
	'''Head normal form of a term'''
	while is_head_reducible(term):
		term = head_reduce(term)
	return term

@lru_cache(maxsize=None)
def normalize(term):
	'''Normal form of a term'''
	if isinstance(term, Constant):
		return term
	elif isinstance(term, Variable):
		return term
	elif isinstance(term, Abstraction):
		if is_head_reducible(term):
			return normalize(head_normalize(term))
		else:
			return Abstraction(term.type, normalize(term.body))
		# return Abstraction(term.type, normalize(term.body))
	elif isinstance(term, Application):
		# Reduce left term (function) first
		term = Application(normalize(term.function), term.argument)
		# Check whether further reduction is necessary
		if is_head_reducible(term):
			after = head_normalize(term)
			return normalize(after)
		else:
			e = Application(normalize(term.function), normalize(term.argument))
			if is_head_reducible(e):
				return normalize(e)
			else:
				return e









@lru_cache(maxsize=None)
def unchurch(term):
	assert isinstance(term, Term)
	if term == Constant('zero'):
		return 0
	elif isinstance(term, Application) and term.function == Constant('succ'):
		return 1 + unchurch(term.argument)
	else:
		raise Exception('Not in church form: {}'.format(term))

@lru_cache(maxsize=None)
def church(number):
	assert isinstance(number, int)
	if number == 0:
		return Constant('zero')
	else:
		return Application(Constant('succ'), church(number - 1))




@lru_cache(maxsize=None)
def type_size(type):
	assert isinstance(type, Type)

	if isinstance(type, BaseType):
		return 0
	elif isinstance(type, FunctionType):
		return 1 + type_size(type.argument) + type_size(type.result)


@lru_cache(maxsize=None)
def size(term):
	assert isinstance(term, Term)

	if isinstance(term, Variable) or isinstance(term, Constant):
		return 0
	elif isinstance(term, Abstraction):
		return 1 + type_size(term.type) + size(term.body)
	elif isinstance(term, Application):
		return 1 + size(term.function) + size(term.argument)











@lru_cache(maxsize=None)
def occurs(variable, term):
	'''Returns whether a variable occurs in a term'''
	assert isinstance(variable, Variable)
	assert isinstance(term, Term)
	if isinstance(term, Constant):
		return False
	elif isinstance(term, Variable):
		return term.index == variable.index
	elif isinstance(term, Abstraction):
		return occurs(Variable(variable.index + 1), term.body)
	elif isinstance(term, Application):
		return occurs(variable, term.function) or occurs(variable, term.argument)

@lru_cache(maxsize=None)
def is_eta_reducible(term):
	assert isinstance(term, Term)
	return isinstance(term, Abstraction) and isinstance(term.body, Application) and term.body.argument == Variable(0) and not occurs(Variable(0), term.body.function)

@lru_cache(maxsize=None)
def eta_reduce(term):
	assert isinstance(term, Term)
	return lift(term.body.function, -1)






@lru_cache(maxsize=None)
def replace(term, occurrence, substitute):
	if term == occurrence:
		return substitute
	elif isinstance(term, Abstraction):
		return Abstraction(term.type, replace(term.body, occurrence, substitute))
	elif isinstance(term, Application):
		return Application(
			replace(term.function, occurrence, substitute),
			replace(term.argument, occurrence, substitute)
		)
	else:
		return term



from random import randint

@lru_cache(maxsize=None)
def inductively_equal_old(f, f_t, g, g_t):

	if f == g:
		return True

	print('f = {}'.format(f))
	print('g = {}\n'.format(g))

	if f_t != g_t:
		print('Type mismatch')
		return False

	f_0 = normalize(Application(f, Constant('zero')))
	g_0 = normalize(Application(g, Constant('zero')))

	print('f(0) = {}'.format(f_0))
	print('g(0) = {}\n'.format(g_0))

	n = Constant('i' + str(randint(0, 100)))
	succ_n = Application(Constant('succ'), n)

	f_n = normalize(Application(f, n))
	g_n = normalize(Application(g, n))

	print('f(n) = {}'.format(f_n))
	print('g(n) = {}\n'.format(g_n))

	f_succ_n = normalize(Application(f, succ_n))
	g_succ_n = normalize(Application(g, succ_n))

	print('f(succ n) = {}'.format(f_succ_n))
	print('g(succ n) = {}\n'.format(g_succ_n))

	replacement = replace(f_succ_n, f_n, g_n)
	print('Inductive f(succ n) = {}\n'.format(replacement))
	inductive_eq = (replacement == g_succ_n)

	if f_0 == g_0 and inductive_eq:
		#print('Match!')
		return True
	else:
		#print('Inductive case mismatch for {} and {}'.format(f, g))
		if isinstance(f_t, FunctionType) and isinstance(g_t, FunctionType):
			return inductively_equal(f_n, f_t.result, g_n, g_t.result)
		else:
			#print('Failed: {} and {}'.format(f, g))
			return False




natural = BaseType('ℕ')

def inductively_equal(f, f_t, g, g_t, log=False):
	return (
		inductively_equal_helper(f, f_t, g, g_t, log) or
		inductively_equal_helper(g, f_t, f, g_t, log)
	)

@lru_cache(maxsize=None)
def inductively_equal_helper(f, f_t, g, g_t, log=False):
	if log:
		print('\nf = {}'.format(f))
		print('g = {}\n'.format(g))
	if f_t == g_t:
		if f_t == natural:
			if normalize(f) == normalize(g):
				return True
			else:
				return False
		elif isinstance(f_t, FunctionType) and f_t.argument == natural:
			f_0 = normalize(Application(f, Constant('zero')))
			g_0 = normalize(Application(g, Constant('zero')))

			n = Constant('${}'.format(randint(0, 1000))) # Greater range = lower false positive rate?
			succ_n = Application(Constant('succ'), n)

			f_n = normalize(Application(f, n))
			g_n = normalize(Application(g, n))

			f_succ_n = normalize(Application(f, succ_n))
			g_succ_n = normalize(Application(g, succ_n))
			
			f_succ_n_rep = replace(f_succ_n, f_n, g_n)

			if log:
				print('f(0) = {}'.format(f_0))
				print('g(0) = {}\n'.format(g_0))

				print('f(n) = {}'.format(f_n))
				print('g(n) = {}\n'.format(g_n))

				print('f(succ n) = {}'.format(f_succ_n))
				print('g(succ n) = {}\n'.format(g_succ_n))

				print('Replaced f(succ n) = {}\n'.format(f_succ_n_rep))

			if not inductively_equal(f_0, f_t.result, g_0, g_t.result):
				if log: print('Base case inequality:\n{}\n{}'.format(f_0, g_0))
				return False
			if not inductively_equal(f_succ_n_rep, f_t.result, g_succ_n, g_t.result):
				if log: print('Inductive case inequality:\n{}\n{}'.format(f_succ_n_rep, g_succ_n))
				return False
			return True
		else:
			return False
	else:
		return False






@lru_cache(maxsize=None)
def eta_reduce(term):
	if isinstance(term, Abstraction) and isinstance(term.body, Application) and term.body.argument == Variable(0) and not occurs(Variable(0), term.body.function):
		return lift(term.body.function, -1)
	else:
		return False

@lru_cache(maxsize=None)
def beta_reduce(term):
	if isinstance(term, Application) and isinstance(term.function, Abstraction):
		return substitution(term.function.body, term.argument)
	else:
		return False

@lru_cache(maxsize=None)
def iter_reduce(term):
	if isinstance(term, Application) and term.function == Constant('iter'):
		if term.argument == Constant('zero'):
			return Abstraction(
				FunctionType(natural, natural),
				Abstraction(
					natural,
					Variable(0)
				)
			)
		elif isinstance(term.argument, Application) and term.argument.function == Constant('succ'):
			i = term.argument.argument
			return Abstraction(
				FunctionType(natural, natural),
				Abstraction(
					natural,
					Application(
						Variable(1),
						Application(
							Application(
								Application(
									Constant('iter'),
									lift(i, 2)
								),
								Variable(1)
							),
							Variable(0)
						)
					)
				)
			)
		else:
			return False
	else:
		return False

@lru_cache(maxsize=None)
def reduce(term):
	'''Returns False if not reducible'''
	reduction = eta_reduce(term) or beta_reduce(term) or iter_reduce(term)
	if reduction is not False:
		return reduction

	if isinstance(term, Abstraction):
		body_reduction = reduce(term.body)
		if body_reduction is False:
			return False
		else:
			return Abstraction(term.type, body_reduction)
	elif isinstance(term, Application):
		function_reduction = reduce(term.function)
		if function_reduction is False:
			argument_reduction = reduce(term.argument)
			if argument_reduction is False:
				return False
			else:
				return Application(term.function, argument_reduction)
		else:
			return Application(function_reduction, term.argument)
	else:
		return False

@lru_cache(maxsize=None)
def normalize(term):
	while True:
		reduction = reduce(term)
		if isinstance(reduction, Term):
			term = reduction
			continue
		else:
			return term








