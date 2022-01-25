note
    explicit: "all"

class
	CLOCK

feature -- Access

	hours: INTEGER
			-- Hours of clock.
	minutes: INTEGER
			-- Minutes of clock.
	seconds: INTEGER
			-- Seconds of clock.

feature -- Element change

	set_hours (a_value: INTEGER)
			-- Set `hours' to `a_value'.
		require
			valid_hours: 0 <= a_value and a_value < 24
		do
			hours := a_value
		ensure
			hours_set: hours = a_value
		end

	set_minutes (a_value: INTEGER)
			-- Set `minutes' to `a_value'.
		require
			valid_minutes: 0 <= a_value and a_value < 60
		do
			minutes := a_value
		ensure
			minutes_set: minutes = a_value
		end

	set_seconds (a_value: INTEGER)
			-- Set `seconds' to `a_value'.
		require
			valid_seconds: 0 <= a_value and a_value < 60
		do
			seconds := a_value
		ensure
			seconds_set: seconds = a_value
		end

feature -- Basic operations

	increase_hours
			-- Increase `hours' by one.
		do
			if hours = 23 then
				set_hours (0)
			else
				set_hours (hours + 1)
			end
		ensure
			hours_increased: hours = (old hours + 1) \\ 24
		end

	increase_minutes
			-- Increase `minutes' by one.
		do
			if minutes < 59 then
				set_minutes (minutes + 1)
			else
				set_minutes (0)
				increase_hours
			end
		ensure
			hours_unchanged: old minutes < 59 implies hours = old hours
			minutes_increased: minutes = (old minutes + 1) \\ 60
			-- hour_increased: old minutes = 59 implies hours = (old hours + 1) \\ 24
		end

	increase_seconds
			-- Increase `seconds' by one.
		do
			if seconds >= 59 then
				set_seconds (0)
				increase_minutes
			else
				set_seconds (seconds + 1)
			end
		ensure
			minutes_unchanged: old seconds < 59 implies minutes = old minutes
			minutes_increased: old seconds = 59 implies minutes = (old minutes + 1) \\ 60
			hours_unchanged: old seconds < 59 or old minutes < 59
			                          implies hours = old hours
			hours_increased: old seconds = 59 and old minutes = 59
			                          implies hours = (old hours + 1) \\ 24
			seconds_increased: seconds = (old seconds + 1) \\ 60
		end

invariant
	hours_valid: 0 <= hours and hours <= 23
	minutes_valid: 0 <= minutes and minutes <= 59
	seconds_valid: 0 <= seconds and seconds <= 59
end

