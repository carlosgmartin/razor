from entities import *
from functools import lru_cache
from reducers import *

@lru_cache(maxsize=None)
def increment(term):
	assert isinstance(term, Term)
	if isinstance(term, Variable):
		return Variable(term.index + 1)
	elif isinstance(term, Application):
		return Application(increment(term.function), increment(term.argument))
	elif isinstance(term, Abstraction):
		return Abstraction(term.type, increment(term.body))
	elif isinstance(term, Constant):
		return term

@lru_cache(maxsize=None)
def augment(context, type):
	assert isinstance(type, Type)
	return ((Variable(0), type),) + tuple(
		(increment(e), t)
		for e, t in context
	)

@lru_cache(maxsize=None)
def abstractions(context, steps):
	assert isinstance(steps, int) and steps >= 0
	return tuple(
		(Abstraction(t, e), FunctionType(t, e_t))
		for n in range(steps)
		for t in types(n)
		for e, e_t in terms(augment(context, t), steps - 1 - n)
	)

@lru_cache(maxsize=None)
def functions(context, steps, argument):
	assert isinstance(steps, int) and steps >= 0
	assert isinstance(argument, Type)
	return tuple(
		(e, t)
		for e, t in terms(context, steps)
		if isinstance(t, FunctionType) and t.argument == argument
	)

@lru_cache(maxsize=None)
def terms(context, steps):
	assert isinstance(steps, int) and steps >= 0

	# Non-debug version
	return context if steps == 0 else tuple(
		(e, t)
		for e, t in abstractions(context, steps) + applications(context, steps)
		if (normalize(e), t) not in normal_forms(context, steps - 1)
		if not any(inductively_equal(e, t, e2, t2) for e2, t2 in normal_forms_type(context, steps - 1, t))
	)
	# Should also make sure that only 1 inductively-equivalent function makes it per round

	'''
	# Debug version
	if steps == 0:
		return context
	else:
		results = tuple(
			(e, t)
			for e, t in
			abstractions(context, steps) + applications(context, steps)
			if (normalize(e), t) not in normal_forms(context, steps - 1)
			if not any(inductively_equal(e, t, e2, t2) for e2, t2 in normal_forms(context, steps - 1))
		)

		#for e, t in results:
		#	for n in range(steps):
		#		for e2, t2 in terms(context, n):
		#			if inductively_equal(e, t, e2, t2):
		#				raise Exception

		#for e, t in results:
		#	if str(e) == '(λ:ℕ (λ:ℕ (((iter 0) succ) 1)))':
		#		#print('{} : {}'.format(e, t))
		#		for n in range(steps):
		#			for e2, t2 in terms(context, n):
		#				if str(e2) == '(λ:ℕ ((iter 0) succ))':
		#					#print('{} : {}'.format(e2, t2))
		#					print('Inductively equal: {}'.format(inductively_equal(e, t, e2, t2, log=True)))
		#					exit()
		#return results
	'''

@lru_cache(maxsize=None)
def normal_forms(context, steps):
	assert isinstance(steps, int) and steps >= 0
	return tuple(
		(() if steps == 0 else normal_forms(context, steps - 1)) +
		tuple((normalize(e), t) for e, t in terms(context, steps))
	)

@lru_cache(maxsize=None)
def normal_forms_type(context, steps, type):
	return tuple(
		(e, t)
		for e, t in normal_forms(context, steps)
		if t == type
	)

@lru_cache(maxsize=None)
def applications(context, steps):
	assert isinstance(steps, int) and steps >= 0
	return tuple(
		(Application(e1, e2), e1_t.result)
		for n in range(steps)
		for e2, e2_t in terms(context, n)
		for e1, e1_t in functions(context, steps - 1 - n, e2_t)
	)

natural = BaseType('\u2115')
penalty = 1

@lru_cache(maxsize=None)
def types(steps):
	assert isinstance(steps, int) and steps >= 0
	return (natural,) if steps == 0 else tuple(
		FunctionType(t1, t2)
		for n in range(steps - penalty + 1)
		for t1 in types(n)
		for t2 in types(steps - penalty - n)
	)



