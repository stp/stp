#ifndef SYMBOLS_H
#define SYMBOLS_H

// Each node is either: empty, an ASTNode, or a vector of more than one child nodes.

class Symbols {
	private:
		Symbols& operator =(const Symbols& other) { /*..*/}
		Symbols(const Symbols& other) {/*..*/}

//		pair<ASTNode,bool> cache;
	public:

		const ASTNode found;
		const vector<Symbols*> children;

		Symbols() {
		}

		Symbols(const ASTNode& n): found(n)
		{
		}

		// This will create an "empty" node if the array is empty.
		Symbols(const vector<Symbols*>& s):
			children(s.begin(), s.end())
		{
			// Children should never be empty. They shouldn't be children.
			for(vector<Symbols*>::const_iterator it = children.begin(); it!= children.end(); it++)
			{
				assert(!(*it)->empty());
			}

			assert(children.size() != 1);
		}

		bool isContained(const ASTNode& n) {
//			if (cache.first == n)
//				return cache.second;

			bool result = false;
			if (!found.IsNull())
				result =  (found == n);
			else {
				for (int i = 0; i < children.size(); i++)
					if (children[i]->isContained(n))
					{
						result =  true;
						break;
					}
			}
//			cache = make_pair(n,result);
			return result;
		}

		bool empty() const {
			return (found.IsNull() && children.size() == 0);
		}


	};

class SymbolPtrHasher
{
public:
  size_t operator()(const Symbols * n) const
  {
    return (size_t) n;
  }
  ;
}; //End of ASTNodeHasher


#endif
