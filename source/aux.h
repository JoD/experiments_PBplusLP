#include <algorithm>
#include <vector>
#include <algorithm>
#include <numeric>

namespace aux{
	template <class T> inline void swapErase(T& indexable, size_t index){
		indexable[index]=indexable.back();
		indexable.pop_back();
	}

	template <class T, class U> inline bool contains(const T& iterable, const U& element){
		for(const U& x: iterable) if(x==element) return true;
		return false;
	}

	template <class T> T median(std::vector<T>& v){
		assert(v.size()>0);
		size_t n = v.size() / 2;
		std::nth_element(v.begin(), v.begin()+n, v.end());
		return v[n];
	}

	template <class T> double average(const std::vector<T>& v){
		assert(v.size()>0);
		return std::accumulate(v.begin(), v.end(), 0.0) / (double) v.size();
	}

	template <class T> T min(const std::vector<T>& v){
		return *std::min_element(v.begin(), v.end());
	}

	template <class T> T max(const std::vector<T>& v){
		return *std::max_element(v.begin(), v.end());
	}
}
