from itertools import count
from entities import *
from generators import *
from reducers import *

natural = BaseType('\u2115')

context = (
	(Constant('zero'), natural),
	(Constant('succ'), FunctionType(natural, natural)),
	(Constant('iter'), FunctionType(natural, FunctionType(FunctionType(natural, natural), FunctionType(natural, natural))))
)

def test(term):
	for a in range(5):
		for b in range(5):
			expression = Application(Application(term, church(a)), church(b))
			result = unchurch(normalize(expression))
			if result not in [a * b]:
				return False
	return True





# Prove that (λ:ℕ (((iter 0) succ) zero)) = (λ:ℕ 0)
'''
f = Abstraction(natural, Application(Application(Application(Constant('iter'), Variable(0)), Constant('succ')), Constant('zero')))
g = Abstraction(natural, Variable(0))
t = FunctionType(natural, natural)
print(inductively_equal(f, t, g, t))
'''


'''
# Prove that multiplication functions
# (λ:ℕ ((iter 0) succ)) and
# (λ:ℕ (λ:ℕ (((iter 0) succ) 1)))
# are (double-)inductively equal
f = Abstraction(natural, 
	Application(
		Application(Constant('iter'), Variable(0)), 
		Constant('succ')
	)
)
g = Abstraction(natural,
	Abstraction(natural,
		Application(Application(Application(Constant('iter'), Variable(0)), Constant('succ')), Variable(1))
	)
)
t = FunctionType(natural, FunctionType(natural, natural))
print('{} : {}'.format(g, t))
print('{} : {}'.format(f, t))
print('Inductively equal: {}\n'.format(inductively_equal(f, t, g, t, log=True)))
'''



for steps in count():
	print('{} steps'.format(steps), end=', ')
	print('{} terms'.format(len(terms(context, steps))))
	#print('Normal forms: {}'.format(normal_forms(context, steps)))

	for e, t in terms(context, steps):
		#print('{} ⟶   {}'.format(e, normalize(e)))
		#continue

		if t == FunctionType(natural, FunctionType(natural, natural)) and test(e):
			print('Candidate function: {}'.format(e))

		continue

		if t == natural:
			print(unchurch(normal_form))

		if t == FunctionType(natural, FunctionType(natural, natural)) and isinstance(e, Abstraction) and isinstance(e.body, Abstraction) and isinstance(e.body.body, Application):
			if str(e) in [
				'(λ:ℕ (λ:ℕ (((iter 0) (λ:ℕ (((iter 0) succ) 2))) zero)))',
				'(λ:ℕ (λ:ℕ (((iter 1) (λ:ℕ (((iter 0) succ) 1))) zero)))'
			]:
				print('Found multiplication')
				print(e)
				print(normalize(e))
